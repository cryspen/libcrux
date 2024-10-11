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

type t_DomainSeparationError = | DomainSeparationError_ContextTooLongError : t_DomainSeparationError

val t_DomainSeparationError_cast_to_repr (x: t_DomainSeparationError)
    : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

class t_PreHash (v_Self: Type0) (v_DIGEST_LEN: usize) = {
  f_oid_pre:Prims.unit -> Type0;
  f_oid_post:Prims.unit -> t_Array u8 (Rust_primitives.mk_usize 11) -> Type0;
  f_oid:x0: Prims.unit
    -> Prims.Pure (t_Array u8 (Rust_primitives.mk_usize 11))
        (f_oid_pre x0)
        (fun result -> f_oid_post x0 result);
  f_hash_pre:t_Slice u8 -> Type0;
  f_hash_post:t_Slice u8 -> t_Array u8 v_DIGEST_LEN -> Type0;
  f_hash:x0: t_Slice u8
    -> Prims.Pure (t_Array u8 v_DIGEST_LEN) (f_hash_pre x0) (fun result -> f_hash_post x0 result)
}

let v_PRE_HASH_OID_LEN: usize = Rust_primitives.mk_usize 11

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
        Libcrux_ml_dsa.Types.VerificationError_ContextTooLongError
        <:
        Libcrux_ml_dsa.Types.t_VerificationError
  }

/// Binds the context string to an optional pre-hash OID identifying
/// the hash function or XOF used for pre-hashing.
type t_DomainSeparationContext = {
  f_context:t_Slice u8;
  f_pre_hash_oid:Core.Option.t_Option (t_Array u8 (Rust_primitives.mk_usize 11))
}

/// Returns the context, guaranteed to be at most 255 bytes long.
val impl_1__context (self: t_DomainSeparationContext)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

/// `context` must be at most 255 bytes long.
val impl_1__new
      (context: t_Slice u8)
      (pre_hash_oid: Core.Option.t_Option (t_Array u8 (Rust_primitives.mk_usize 11)))
    : Prims.Pure (Core.Result.t_Result t_DomainSeparationContext t_DomainSeparationError)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Returns the pre-hash OID, if any.
val impl_1__pre_hash_oid (self: t_DomainSeparationContext)
    : Prims.Pure (Core.Option.t_Option (t_Array u8 (Rust_primitives.mk_usize 11)))
      Prims.l_True
      (fun _ -> Prims.l_True)

/// An implementation of the pre-hash trait for the SHAKE-128 XOF with
/// digest length 256 bytes.
type t_SHAKE128_PH = | SHAKE128_PH : t_SHAKE128_PH

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_PreHash t_SHAKE128_PH (Rust_primitives.mk_usize 256) =
  {
    f_oid_pre = (fun (_: Prims.unit) -> true);
    f_oid_post = (fun (_: Prims.unit) (out: t_Array u8 (Rust_primitives.mk_usize 11)) -> true);
    f_oid
    =
    (fun (_: Prims.unit) ->
        let list =
          [
            Rust_primitives.mk_u8 6; Rust_primitives.mk_u8 9; Rust_primitives.mk_u8 96;
            Rust_primitives.mk_u8 134; Rust_primitives.mk_u8 72; Rust_primitives.mk_u8 1;
            Rust_primitives.mk_u8 101; Rust_primitives.mk_u8 3; Rust_primitives.mk_u8 4;
            Rust_primitives.mk_u8 2; Rust_primitives.mk_u8 11
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 11);
        Rust_primitives.Hax.array_of_list 11 list);
    f_hash_pre = (fun (message: t_Slice u8) -> true);
    f_hash_post
    =
    (fun (message: t_Slice u8) (out: t_Array u8 (Rust_primitives.mk_usize 256)) -> true);
    f_hash
    =
    fun (message: t_Slice u8) ->
      let output:t_Array u8 (Rust_primitives.mk_usize 256) =
        Rust_primitives.Hax.repeat (Rust_primitives.mk_u8 0) (Rust_primitives.mk_usize 256)
      in
      let output:t_Array u8 (Rust_primitives.mk_usize 256) =
        Libcrux_ml_dsa.Hash_functions.Shake128.f_shake128 #Libcrux_ml_dsa.Hash_functions.Portable.t_Shake128
          #FStar.Tactics.Typeclasses.solve
          (Rust_primitives.mk_usize 256)
          message
          output
      in
      output
  }
