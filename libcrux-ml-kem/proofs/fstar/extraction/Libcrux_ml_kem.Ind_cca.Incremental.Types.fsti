module Libcrux_ml_kem.Ind_cca.Incremental.Types
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Ind_cpa.Unpacked in
  let open Libcrux_ml_kem.Vector.Traits in
  ()

/// Errors
type t_Error =
  | Error_InvalidInputLength : t_Error
  | Error_InvalidOutputLength : t_Error
  | Error_InvalidPublicKey : t_Error

val t_Error_cast_to_repr (x: t_Error) : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_16:Core.Fmt.t_Debug t_Error

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_17:Core.Clone.t_Clone t_Error

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_18:Core.Marker.t_Copy t_Error

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_19:Core.Marker.t_StructuralPartialEq t_Error

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_20:Core.Cmp.t_PartialEq t_Error t_Error

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_21:Core.Cmp.t_Eq t_Error

/// Incremental trait for unpacked key pairs.
class t_IncrementalKeyPair (v_Self: Type0) = {
  f_pk1_bytes_pre:v_Self -> t_Slice u8 -> Type0;
  f_pk1_bytes_post:v_Self -> t_Slice u8 -> (t_Slice u8 & Core.Result.t_Result Prims.unit t_Error)
    -> Type0;
  f_pk1_bytes:x0: v_Self -> x1: t_Slice u8
    -> Prims.Pure (t_Slice u8 & Core.Result.t_Result Prims.unit t_Error)
        (f_pk1_bytes_pre x0 x1)
        (fun result -> f_pk1_bytes_post x0 x1 result);
  f_pk2_bytes_pre:v_Self -> t_Slice u8 -> Type0;
  f_pk2_bytes_post:v_Self -> t_Slice u8 -> t_Slice u8 -> Type0;
  f_pk2_bytes:x0: v_Self -> x1: t_Slice u8
    -> Prims.Pure (t_Slice u8) (f_pk2_bytes_pre x0 x1) (fun result -> f_pk2_bytes_post x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl
      (v_K: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
    : t_IncrementalKeyPair (Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K v_Vector)

/// The incremental public key that allows generating [`Ciphertext1`].
type t_PublicKey1 = {
  f_seed:t_Array u8 (mk_usize 32);
  f_hash:t_Array u8 (mk_usize 32)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_22:Core.Default.t_Default t_PublicKey1

/// Get the size of the first public key in bytes.
val impl_PublicKey1__len: Prims.unit -> Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Core.Convert.t_TryFrom t_PublicKey1 (t_Slice u8) =
  {
    f_Error = t_Error;
    f_try_from_pre = (fun (value: t_Slice u8) -> true);
    f_try_from_post
    =
    (fun (value: t_Slice u8) (out: Core.Result.t_Result t_PublicKey1 t_Error) -> true);
    f_try_from
    =
    fun (value: t_Slice u8) ->
      if (Core.Slice.impl__len #u8 value <: usize) <. mk_usize 64
      then
        Core.Result.Result_Err (Error_InvalidInputLength <: t_Error)
        <:
        Core.Result.t_Result t_PublicKey1 t_Error
      else
        let seed:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
        let seed:t_Array u8 (mk_usize 32) =
          Core.Slice.impl__copy_from_slice #u8
            seed
            (value.[ { Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 32 }
                <:
                Core.Ops.Range.t_Range usize ]
              <:
              t_Slice u8)
        in
        let hash:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
        let hash:t_Array u8 (mk_usize 32) =
          Core.Slice.impl__copy_from_slice #u8
            hash
            (value.[ { Core.Ops.Range.f_start = mk_usize 32; Core.Ops.Range.f_end = mk_usize 64 }
                <:
                Core.Ops.Range.t_Range usize ]
              <:
              t_Slice u8)
        in
        Core.Result.Result_Ok ({ f_seed = seed; f_hash = hash } <: t_PublicKey1)
        <:
        Core.Result.t_Result t_PublicKey1 t_Error
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_3:Core.Convert.t_From t_PublicKey1 (t_Array u8 (mk_usize 64))

/// The incremental public key that allows generating [`Ciphertext2`].
/// This public key is serialized to safe bytes on the wire.
type t_PublicKey2 (v_LEN: usize) = { f_tt_as_ntt:t_Array u8 v_LEN }

/// Get the size of the second public key in bytes.
val impl_4__len: v_LEN: usize -> Prims.unit -> Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// Deserialize the public key.
val impl_4__deserialize
      (v_LEN v_K: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self: t_PublicKey2 v_LEN)
    : Prims.Pure (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Trait container for multiplexing over platform dependent [`MlKemKeyPairUnpacked`].
class t_Keys (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_13302654320391107453:t_IncrementalKeyPair v_Self;
  f_as_any_pre:v_Self -> Type0;
  f_as_any_post:v_Self -> dyn 1 (fun z -> Core.Any.t_Any z) -> Type0;
  f_as_any:x0: v_Self
    -> Prims.Pure (dyn 1 (fun z -> Core.Any.t_Any z))
        (f_as_any_pre x0)
        (fun result -> f_as_any_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_5
      (v_K: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
    : t_Keys (Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K v_Vector)

/// The partial ciphertext c1 - first part.
type t_Ciphertext1 (v_LEN: usize) = { f_value:t_Array u8 v_LEN }

/// The size of the ciphertext.
val impl_6__len: v_LEN: usize -> Prims.unit -> Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// The partial ciphertext c2 - second part.
type t_Ciphertext2 (v_LEN: usize) = { f_value:t_Array u8 v_LEN }

/// The size of the ciphertext.
val impl_7__len: v_LEN: usize -> Prims.unit -> Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// The incremental state for encapsulate.
type t_EncapsState
  (v_K: usize) (v_Vector: Type0) {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
  = {
  f_r_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K;
  f_error2:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector;
  f_randomness:t_Array u8 (mk_usize 32)
}

/// Get the number of bytes, required for the state.
val impl_8__num_bytes:
    v_K: usize ->
    #v_Vector: Type0 ->
    {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |} ->
    Prims.unit
  -> Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// Get the state as bytes
val impl_8__to_bytes
      (v_K: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self: t_EncapsState v_K v_Vector)
      (state: t_Slice u8)
    : Prims.Pure (t_Slice u8 & Core.Result.t_Result Prims.unit t_Error)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Build a state from bytes
val impl_8__from_bytes
      (v_K: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (bytes: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result (t_EncapsState v_K v_Vector) t_Error)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Trait container for multiplexing over platform dependent [`EncapsState`].
class t_State (v_Self: Type0) = {
  f_as_any_pre:v_Self -> Type0;
  f_as_any_post:v_Self -> dyn 1 (fun z -> Core.Any.t_Any z) -> Type0;
  f_as_any:x0: v_Self
    -> Prims.Pure (dyn 1 (fun z -> Core.Any.t_Any z))
        (f_as_any_pre x0)
        (fun result -> f_as_any_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_9
      (v_K: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
    : t_State (t_EncapsState v_K v_Vector)

/// Convert [`MlKemPublicKeyUnpacked`] to a [`PublicKey1`]
[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_10
      (v_K: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
    : Core.Convert.t_From t_PublicKey1
      (Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked v_K v_Vector)

/// Convert [`MlKemPublicKeyUnpacked`] to a [`PublicKey2`].
[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_11
      (v_K v_LEN: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
    : Core.Convert.t_From (t_PublicKey2 v_LEN)
      (Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked v_K v_Vector)

/// Convert a byte slice `&[u8]` to a [`PublicKey2`].
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_12 (v_LEN: usize) : Core.Convert.t_TryFrom (t_PublicKey2 v_LEN) (t_Slice u8) =
  {
    f_Error = t_Error;
    f_try_from_pre = (fun (value: t_Slice u8) -> true);
    f_try_from_post
    =
    (fun (value: t_Slice u8) (out: Core.Result.t_Result (t_PublicKey2 v_LEN) t_Error) -> true);
    f_try_from
    =
    fun (value: t_Slice u8) ->
      if (Core.Slice.impl__len #u8 value <: usize) <. v_LEN
      then
        Core.Result.Result_Err (Error_InvalidInputLength <: t_Error)
        <:
        Core.Result.t_Result (t_PublicKey2 v_LEN) t_Error
      else
        let tt_as_ntt:t_Array u8 v_LEN = Rust_primitives.Hax.repeat (mk_u8 0) v_LEN in
        let tt_as_ntt:t_Array u8 v_LEN =
          Core.Slice.impl__copy_from_slice #u8
            tt_as_ntt
            (value.[ { Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = v_LEN }
                <:
                Core.Ops.Range.t_Range usize ]
              <:
              t_Slice u8)
        in
        Core.Result.Result_Ok ({ f_tt_as_ntt = tt_as_ntt } <: t_PublicKey2 v_LEN)
        <:
        Core.Result.t_Result (t_PublicKey2 v_LEN) t_Error
  }

type t_KeyPair
  (v_K: usize) (v_PK2_LEN: usize) (v_Vector: Type0)
  {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
  = {
  f_pk1:t_PublicKey1;
  f_pk2:t_PublicKey2 v_PK2_LEN;
  f_sk:Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPrivateKeyUnpacked v_K v_Vector;
  f_matrix:t_Array (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_13
      (v_K v_PK2_LEN: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
    : Core.Convert.t_From (t_KeyPair v_K v_PK2_LEN v_Vector)
      (Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K v_Vector)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_14
      (v_K v_PK2_LEN: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
    : Core.Convert.t_From (Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K v_Vector)
      (t_KeyPair v_K v_PK2_LEN v_Vector)

/// Get [`PublicKey1`] as bytes.
val impl_15__pk1_bytes
      (v_K v_PK2_LEN: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self: t_KeyPair v_K v_PK2_LEN v_Vector)
      (pk1: t_Slice u8)
    : Prims.Pure (t_Slice u8 & Core.Result.t_Result Prims.unit t_Error)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Get [`PublicKey2`] as bytes.
val impl_15__pk2_bytes
      (v_K v_PK2_LEN: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self: t_KeyPair v_K v_PK2_LEN v_Vector)
      (pk2: t_Slice u8)
    : Prims.Pure (t_Slice u8 & Core.Result.t_Result Prims.unit t_Error)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// The byte size of this key pair.
val impl_15__num_bytes:
    v_K: usize ->
    v_PK2_LEN: usize ->
    #v_Vector: Type0 ->
    {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |} ->
    Prims.unit
  -> Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// Read a key pair from the `key` bytes.
/// `key` must be at least of length `num_bytes()`
val impl_15__from_bytes
      (v_K v_PK2_LEN: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (key: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result (t_KeyPair v_K v_PK2_LEN v_Vector) t_Error)
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl_15__to_bytes__write (out value: t_Slice u8) (offset: usize)
    : Prims.Pure (t_Slice u8 & usize) Prims.l_True (fun _ -> Prims.l_True)

/// Write this key pair into the `key` bytes.
/// `key` must be at least of length `num_bytes()`
val impl_15__to_bytes
      (v_K v_PK2_LEN: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self: t_KeyPair v_K v_PK2_LEN v_Vector)
      (key: t_Slice u8)
    : Prims.Pure (t_Slice u8 & Core.Result.t_Result Prims.unit t_Error)
      Prims.l_True
      (fun _ -> Prims.l_True)
