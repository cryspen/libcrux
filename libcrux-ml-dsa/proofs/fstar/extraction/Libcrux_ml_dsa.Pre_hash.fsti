module Libcrux_ml_dsa.Pre_hash
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
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

val t_DomainSeparationError_cast_to_repr (x: t_DomainSeparationError)
    : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

class t_PreHash (v_Self: Type0) = {
  f_oid_pre:Prims.unit -> Type0;
  f_oid_post:Prims.unit -> t_Array u8 (sz 11) -> Type0;
  f_oid:x0: Prims.unit
    -> Prims.Pure (t_Array u8 (sz 11)) (f_oid_pre x0) (fun result -> f_oid_post x0 result);
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

let v_PRE_HASH_OID_LEN: usize = sz 11

let v_SHAKE128_OID: t_Array u8 (sz 11) =
  let list = [6uy; 9uy; 96uy; 134uy; 72uy; 1uy; 101uy; 3uy; 4uy; 2uy; 11uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 11);
  Rust_primitives.Hax.array_of_list 11 list

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_2:Core.Convert.t_From Libcrux_ml_dsa.Types.t_SigningError t_DomainSeparationError

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_3:Core.Convert.t_From Libcrux_ml_dsa.Types.t_VerificationError t_DomainSeparationError

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl:t_PreHash t_SHAKE128_PH

/// `context` must be at most 255 bytes long.
val impl_1__new (context: t_Slice u8) (pre_hash_oid: Core.Option.t_Option (t_Array u8 (sz 11)))
    : Prims.Pure (Core.Result.t_Result t_DomainSeparationContext t_DomainSeparationError)
      Prims.l_True
      (fun _ -> Prims.l_True)
