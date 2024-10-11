module Libcrux_ml_dsa.Pre_hash
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Hash_functions.Portable in
  let open Libcrux_ml_dsa.Hash_functions.Shake128 in
  ()

let t_DomainSeparationError_cast_to_repr (x: t_DomainSeparationError) =
  match x with | DomainSeparationError_ContextTooLongError  -> Rust_primitives.mk_isize 0

let impl_1__context (self: t_DomainSeparationContext) = self.f_context

let impl_1__new
      (context: t_Slice u8)
      (pre_hash_oid: Core.Option.t_Option (t_Array u8 (Rust_primitives.mk_usize 11)))
     =
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

let impl_1__pre_hash_oid (self: t_DomainSeparationContext) = self.f_pre_hash_oid
