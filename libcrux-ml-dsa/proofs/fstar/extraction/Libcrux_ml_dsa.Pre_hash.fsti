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

/// Binds the context string to an optional pre-hash OID identifying
/// the hash function or XOF used for pre-hashing.
type t_DomainSeparationContext = {
  f_context:t_Slice u8;
  f_pre_hash_oid:Core.Option.t_Option (t_Array u8 (sz 11))
}

/// Returns the context, guaranteed to be at most 255 bytes long.
val impl_1__context (self: t_DomainSeparationContext)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

/// Returns the pre-hash OID, if any.
val impl_1__pre_hash_oid (self: t_DomainSeparationContext)
    : Prims.Pure (Core.Option.t_Option (t_Array u8 (sz 11))) Prims.l_True (fun _ -> Prims.l_True)

type t_DomainSeparationError = | DomainSeparationError_ContextTooLongError : t_DomainSeparationError

/// `context` must be at most 255 bytes long.
val impl_1__new (context: t_Slice u8) (pre_hash_oid: Core.Option.t_Option (t_Array u8 (sz 11)))
    : Prims.Pure (Core.Result.t_Result t_DomainSeparationContext t_DomainSeparationError)
      Prims.l_True
      (fun _ -> Prims.l_True)

val t_DomainSeparationError_cast_to_repr (x: t_DomainSeparationError)
    : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

class t_PreHash (v_Self: Type0) (v_DIGEST_LEN: usize) = {
  f_oid_pre:Prims.unit -> Type0;
  f_oid_post:Prims.unit -> t_Array u8 (sz 11) -> Type0;
  f_oid:x0: Prims.unit
    -> Prims.Pure (t_Array u8 (sz 11)) (f_oid_pre x0) (fun result -> f_oid_post x0 result);
  f_hash_pre:t_Slice u8 -> Type0;
  f_hash_post:t_Slice u8 -> t_Array u8 v_DIGEST_LEN -> Type0;
  f_hash:x0: t_Slice u8
    -> Prims.Pure (t_Array u8 v_DIGEST_LEN) (f_hash_pre x0) (fun result -> f_hash_post x0 result)
}

/// An implementation of the pre-hash trait for the SHAKE-128 XOF with
/// digest length 256 bytes.
type t_SHAKE128_PH = | SHAKE128_PH : t_SHAKE128_PH

let v_PRE_HASH_OID_LEN: usize = sz 11

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_2:Core.Convert.t_From Libcrux_ml_dsa.Types.t_SigningError t_DomainSeparationError

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_3:Core.Convert.t_From Libcrux_ml_dsa.Types.t_VerificationError t_DomainSeparationError

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl:t_PreHash t_SHAKE128_PH (sz 256)
