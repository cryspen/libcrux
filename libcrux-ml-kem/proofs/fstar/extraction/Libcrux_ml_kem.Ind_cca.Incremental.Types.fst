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

let t_Error_cast_to_repr (x: t_Error) =
  match x <: t_Error with
  | Error_InvalidInputLength  -> mk_isize 0
  | Error_InvalidOutputLength  -> mk_isize 1
  | Error_InvalidPublicKey  -> mk_isize 3

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_16': Core.Fmt.t_Debug t_Error

let impl_16 = impl_16'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_17': Core.Clone.t_Clone t_Error

let impl_17 = impl_17'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_18': Core.Marker.t_Copy t_Error

let impl_18 = impl_18'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_19': Core.Marker.t_StructuralPartialEq t_Error

let impl_19 = impl_19'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_20': Core.Cmp.t_PartialEq t_Error t_Error

let impl_20 = impl_20'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_21': Core.Cmp.t_Eq t_Error

let impl_21 = impl_21'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
    : t_IncrementalKeyPair (Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K v_Vector) =
  {
    f_pk1_bytes_pre
    =
    (fun
        (self: Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K v_Vector)
        (bytes: t_Slice u8)
        ->
        true);
    f_pk1_bytes_post
    =
    (fun
        (self: Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K v_Vector)
        (bytes: t_Slice u8)
        (out: (t_Slice u8 & Core.Result.t_Result Prims.unit t_Error))
        ->
        true);
    f_pk1_bytes
    =
    (fun
        (self: Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K v_Vector)
        (bytes: t_Slice u8)
        ->
        let _:Prims.unit =
          if true
          then
            let _:Prims.unit =
              Hax_lib.v_assert ((Core.Slice.impl__len #u8 bytes <: usize) >=. mk_usize 64 <: bool)
            in
            ()
        in
        if (Core.Slice.impl__len #u8 bytes <: usize) <. mk_usize 64
        then
          bytes,
          (Core.Result.Result_Err (Error_InvalidOutputLength <: t_Error)
            <:
            Core.Result.t_Result Prims.unit t_Error)
          <:
          (t_Slice u8 & Core.Result.t_Result Prims.unit t_Error)
        else
          let bytes:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range bytes
              ({ Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 32 }
                <:
                Core.Ops.Range.t_Range usize)
              (Core.Slice.impl__copy_from_slice #u8
                  (bytes.[ {
                        Core.Ops.Range.f_start = mk_usize 0;
                        Core.Ops.Range.f_end = mk_usize 32
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  ((Libcrux_ml_kem.Ind_cca.Unpacked.impl_4__public_key v_K #v_Vector self)
                      .Libcrux_ml_kem.Ind_cca.Unpacked.f_ind_cpa_public_key
                      .Libcrux_ml_kem.Ind_cpa.Unpacked.f_seed_for_A
                    <:
                    t_Slice u8)
                <:
                t_Slice u8)
          in
          let bytes:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range bytes
              ({ Core.Ops.Range.f_start = mk_usize 32; Core.Ops.Range.f_end = mk_usize 64 }
                <:
                Core.Ops.Range.t_Range usize)
              (Core.Slice.impl__copy_from_slice #u8
                  (bytes.[ {
                        Core.Ops.Range.f_start = mk_usize 32;
                        Core.Ops.Range.f_end = mk_usize 64
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  ((Libcrux_ml_kem.Ind_cca.Unpacked.impl_4__public_key v_K #v_Vector self)
                      .Libcrux_ml_kem.Ind_cca.Unpacked.f_public_key_hash
                    <:
                    t_Slice u8)
                <:
                t_Slice u8)
          in
          let hax_temp_output:Core.Result.t_Result Prims.unit t_Error =
            Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit t_Error
          in
          bytes, hax_temp_output <: (t_Slice u8 & Core.Result.t_Result Prims.unit t_Error));
    f_pk2_bytes_pre
    =
    (fun
        (self: Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K v_Vector)
        (bytes: t_Slice u8)
        ->
        true);
    f_pk2_bytes_post
    =
    (fun
        (self: Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K v_Vector)
        (bytes: t_Slice u8)
        (out: t_Slice u8)
        ->
        true);
    f_pk2_bytes
    =
    fun
      (self: Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K v_Vector)
      (bytes: t_Slice u8)
      ->
      let bytes:t_Slice u8 =
        Libcrux_ml_kem.Ind_cpa.serialize_vector v_K
          #v_Vector
          self.Libcrux_ml_kem.Ind_cca.Unpacked.f_public_key
            .Libcrux_ml_kem.Ind_cca.Unpacked.f_ind_cpa_public_key
            .Libcrux_ml_kem.Ind_cpa.Unpacked.f_tt_as_ntt
          bytes
      in
      bytes
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_22': Core.Default.t_Default t_PublicKey1

let impl_22 = impl_22'

let impl_PublicKey1__len (_: Prims.unit) = mk_usize 32 +! mk_usize 32

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Core.Convert.t_From t_PublicKey1 (t_Array u8 (mk_usize 64)) =
  {
    f_from_pre = (fun (value: t_Array u8 (mk_usize 64)) -> true);
    f_from_post = (fun (value: t_Array u8 (mk_usize 64)) (out: t_PublicKey1) -> true);
    f_from
    =
    fun (value: t_Array u8 (mk_usize 64)) ->
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
      { f_seed = seed; f_hash = hash } <: t_PublicKey1
  }

let impl_4__len (v_LEN: usize) (_: Prims.unit) = v_LEN

let impl_4__deserialize
      (v_LEN v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self: t_PublicKey2 v_LEN)
     = Libcrux_ml_kem.Ind_cpa.deserialize_vector v_K #v_Vector (self.f_tt_as_ntt <: t_Slice u8)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
    : t_Keys (Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K v_Vector) =
  {
    _super_13302654320391107453 = FStar.Tactics.Typeclasses.solve;
    f_as_any_pre
    =
    (fun (self: Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K v_Vector) -> true);
    f_as_any_post
    =
    (fun
        (self: Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K v_Vector)
        (out: dyn 1 (fun z -> Core.Any.t_Any z))
        ->
        true);
    f_as_any
    =
    fun (self: Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K v_Vector) ->
      Rust_primitives.unsize (Rust_primitives.unsize self <: dyn 1 (fun z -> Core.Any.t_Any z))
  }

let impl_6__len (v_LEN: usize) (_: Prims.unit) = v_LEN

let impl_7__len (v_LEN: usize) (_: Prims.unit) = v_LEN

let impl_8__num_bytes
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (_: Prims.unit)
     =
  ((Libcrux_ml_kem.Polynomial.vec_len_bytes v_K #v_Vector () <: usize) +!
    (Libcrux_ml_kem.Polynomial.impl_2__num_bytes #v_Vector () <: usize)
    <:
    usize) +!
  mk_usize 32

let impl_8__to_bytes
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self: t_EncapsState v_K v_Vector)
      (state: t_Slice u8)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 state <: usize) >=.
            (impl_8__num_bytes v_K #v_Vector () <: usize)
            <:
            bool)
      in
      ()
  in
  if (Core.Slice.impl__len #u8 state <: usize) <. (impl_8__num_bytes v_K #v_Vector () <: usize)
  then
    state,
    (Core.Result.Result_Err (Error_InvalidOutputLength <: t_Error)
      <:
      Core.Result.t_Result Prims.unit t_Error)
    <:
    (t_Slice u8 & Core.Result.t_Result Prims.unit t_Error)
  else
    let offset:usize = mk_usize 0 in
    let state:t_Slice u8 =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from state
        ({ Core.Ops.Range.f_start = offset } <: Core.Ops.Range.t_RangeFrom usize)
        (Libcrux_ml_kem.Polynomial.vec_to_bytes #v_Vector
            (self.f_r_as_ntt <: t_Slice (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
            )
            (state.[ { Core.Ops.Range.f_start = offset } <: Core.Ops.Range.t_RangeFrom usize ]
              <:
              t_Slice u8)
          <:
          t_Slice u8)
    in
    let offset:usize =
      offset +! (Libcrux_ml_kem.Polynomial.vec_len_bytes v_K #v_Vector () <: usize)
    in
    let state:t_Slice u8 =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from state
        ({ Core.Ops.Range.f_start = offset } <: Core.Ops.Range.t_RangeFrom usize)
        (Libcrux_ml_kem.Polynomial.impl_2__to_bytes #v_Vector
            self.f_error2
            (state.[ { Core.Ops.Range.f_start = offset } <: Core.Ops.Range.t_RangeFrom usize ]
              <:
              t_Slice u8)
          <:
          t_Slice u8)
    in
    let offset:usize =
      offset +! (Libcrux_ml_kem.Polynomial.impl_2__num_bytes #v_Vector () <: usize)
    in
    let state:t_Slice u8 =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_range state
        ({ Core.Ops.Range.f_start = offset; Core.Ops.Range.f_end = offset +! mk_usize 32 <: usize }
          <:
          Core.Ops.Range.t_Range usize)
        (Core.Slice.impl__copy_from_slice #u8
            (state.[ {
                  Core.Ops.Range.f_start = offset;
                  Core.Ops.Range.f_end = offset +! mk_usize 32 <: usize
                }
                <:
                Core.Ops.Range.t_Range usize ]
              <:
              t_Slice u8)
            (self.f_randomness <: t_Slice u8)
          <:
          t_Slice u8)
    in
    let hax_temp_output:Core.Result.t_Result Prims.unit t_Error =
      Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit t_Error
    in
    state, hax_temp_output <: (t_Slice u8 & Core.Result.t_Result Prims.unit t_Error)

let impl_8__from_bytes
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (bytes: t_Slice u8)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 bytes <: usize) >=.
            (impl_8__num_bytes v_K #v_Vector () <: usize)
            <:
            bool)
      in
      ()
  in
  if (Core.Slice.impl__len #u8 bytes <: usize) <. (impl_8__num_bytes v_K #v_Vector () <: usize)
  then
    Core.Result.Result_Err (Error_InvalidInputLength <: t_Error)
    <:
    Core.Result.t_Result (t_EncapsState v_K v_Vector) t_Error
  else
    let offset:usize = mk_usize 0 in
    let r_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
      Core.Array.from_fn #(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
        v_K
        (fun temp_0_ ->
            let _:usize = temp_0_ in
            Libcrux_ml_kem.Polynomial.impl_2__ZERO #v_Vector ()
            <:
            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
    in
    let r_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
      Libcrux_ml_kem.Polynomial.vec_from_bytes #v_Vector
        (bytes.[ { Core.Ops.Range.f_start = offset } <: Core.Ops.Range.t_RangeFrom usize ]
          <:
          t_Slice u8)
        r_as_ntt
    in
    let offset:usize =
      offset +! (Libcrux_ml_kem.Polynomial.vec_len_bytes v_K #v_Vector () <: usize)
    in
    let error2:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
      Libcrux_ml_kem.Polynomial.impl_2__from_bytes #v_Vector
        (bytes.[ { Core.Ops.Range.f_start = offset } <: Core.Ops.Range.t_RangeFrom usize ]
          <:
          t_Slice u8)
    in
    let offset:usize =
      offset +! (Libcrux_ml_kem.Polynomial.impl_2__num_bytes #v_Vector () <: usize)
    in
    let randomness:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
    let randomness:t_Array u8 (mk_usize 32) =
      Core.Slice.impl__copy_from_slice #u8
        randomness
        (bytes.[ {
              Core.Ops.Range.f_start = offset;
              Core.Ops.Range.f_end = offset +! mk_usize 32 <: usize
            }
            <:
            Core.Ops.Range.t_Range usize ]
          <:
          t_Slice u8)
    in
    Core.Result.Result_Ok
    ({ f_r_as_ntt = r_as_ntt; f_error2 = error2; f_randomness = randomness }
      <:
      t_EncapsState v_K v_Vector)
    <:
    Core.Result.t_Result (t_EncapsState v_K v_Vector) t_Error

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
    : t_State (t_EncapsState v_K v_Vector) =
  {
    f_as_any_pre = (fun (self: t_EncapsState v_K v_Vector) -> true);
    f_as_any_post
    =
    (fun (self: t_EncapsState v_K v_Vector) (out: dyn 1 (fun z -> Core.Any.t_Any z)) -> true);
    f_as_any
    =
    fun (self: t_EncapsState v_K v_Vector) ->
      Rust_primitives.unsize (Rust_primitives.unsize self <: dyn 1 (fun z -> Core.Any.t_Any z))
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
    : Core.Convert.t_From t_PublicKey1
      (Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked v_K v_Vector) =
  {
    f_from_pre
    =
    (fun (pk: Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked v_K v_Vector) -> true);
    f_from_post
    =
    (fun
        (pk: Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked v_K v_Vector)
        (out: t_PublicKey1)
        ->
        true);
    f_from
    =
    fun (pk: Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked v_K v_Vector) ->
      {
        f_seed
        =
        pk.Libcrux_ml_kem.Ind_cca.Unpacked.f_ind_cpa_public_key
          .Libcrux_ml_kem.Ind_cpa.Unpacked.f_seed_for_A;
        f_hash = pk.Libcrux_ml_kem.Ind_cca.Unpacked.f_public_key_hash
      }
      <:
      t_PublicKey1
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11
      (v_K v_LEN: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
    : Core.Convert.t_From (t_PublicKey2 v_LEN)
      (Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked v_K v_Vector) =
  {
    f_from_pre
    =
    (fun (pk: Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked v_K v_Vector) -> true);
    f_from_post
    =
    (fun
        (pk: Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked v_K v_Vector)
        (out1: t_PublicKey2 v_LEN)
        ->
        true);
    f_from
    =
    fun (pk: Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked v_K v_Vector) ->
      let out:t_PublicKey2 v_LEN =
        { f_tt_as_ntt = Rust_primitives.Hax.repeat (mk_u8 0) v_LEN } <: t_PublicKey2 v_LEN
      in
      let out:t_PublicKey2 v_LEN =
        {
          out with
          f_tt_as_ntt
          =
          Libcrux_ml_kem.Ind_cpa.serialize_vector v_K
            #v_Vector
            pk.Libcrux_ml_kem.Ind_cca.Unpacked.f_ind_cpa_public_key
              .Libcrux_ml_kem.Ind_cpa.Unpacked.f_tt_as_ntt
            out.f_tt_as_ntt
        }
        <:
        t_PublicKey2 v_LEN
      in
      out
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_13
      (v_K v_PK2_LEN: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
    : Core.Convert.t_From (t_KeyPair v_K v_PK2_LEN v_Vector)
      (Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K v_Vector) =
  {
    f_from_pre
    =
    (fun (kp: Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K v_Vector) -> true);
    f_from_post
    =
    (fun
        (kp: Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K v_Vector)
        (out: t_KeyPair v_K v_PK2_LEN v_Vector)
        ->
        true);
    f_from
    =
    fun (kp: Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K v_Vector) ->
      {
        f_pk1
        =
        Core.Convert.f_from #t_PublicKey1
          #(Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked v_K v_Vector)
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_ml_kem.Ind_cca.Unpacked.impl_4__public_key v_K #v_Vector kp
            <:
            Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked v_K v_Vector);
        f_pk2
        =
        Core.Convert.f_from #(t_PublicKey2 v_PK2_LEN)
          #(Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked v_K v_Vector)
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_ml_kem.Ind_cca.Unpacked.impl_4__public_key v_K #v_Vector kp
            <:
            Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked v_K v_Vector);
        f_sk = kp.Libcrux_ml_kem.Ind_cca.Unpacked.f_private_key;
        f_matrix
        =
        kp.Libcrux_ml_kem.Ind_cca.Unpacked.f_public_key
          .Libcrux_ml_kem.Ind_cca.Unpacked.f_ind_cpa_public_key
          .Libcrux_ml_kem.Ind_cpa.Unpacked.f_A
      }
      <:
      t_KeyPair v_K v_PK2_LEN v_Vector
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_14
      (v_K v_PK2_LEN: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
    : Core.Convert.t_From (Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K v_Vector)
      (t_KeyPair v_K v_PK2_LEN v_Vector) =
  {
    f_from_pre = (fun (value: t_KeyPair v_K v_PK2_LEN v_Vector) -> true);
    f_from_post
    =
    (fun
        (value: t_KeyPair v_K v_PK2_LEN v_Vector)
        (out: Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K v_Vector)
        ->
        true);
    f_from
    =
    fun (value: t_KeyPair v_K v_PK2_LEN v_Vector) ->
      {
        Libcrux_ml_kem.Ind_cca.Unpacked.f_private_key = value.f_sk;
        Libcrux_ml_kem.Ind_cca.Unpacked.f_public_key
        =
        {
          Libcrux_ml_kem.Ind_cca.Unpacked.f_ind_cpa_public_key
          =
          {
            Libcrux_ml_kem.Ind_cpa.Unpacked.f_tt_as_ntt
            =
            Libcrux_ml_kem.Ind_cpa.deserialize_vector v_K
              #v_Vector
              (value.f_pk2.f_tt_as_ntt <: t_Slice u8);
            Libcrux_ml_kem.Ind_cpa.Unpacked.f_seed_for_A = value.f_pk1.f_seed;
            Libcrux_ml_kem.Ind_cpa.Unpacked.f_A = value.f_matrix
          }
          <:
          Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector;
          Libcrux_ml_kem.Ind_cca.Unpacked.f_public_key_hash = value.f_pk1.f_hash
        }
        <:
        Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked v_K v_Vector
      }
      <:
      Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K v_Vector
  }

let impl_15__pk1_bytes
      (v_K v_PK2_LEN: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self: t_KeyPair v_K v_PK2_LEN v_Vector)
      (pk1: t_Slice u8)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 pk1 <: usize) >=.
            (impl_PublicKey1__len () <: usize)
            <:
            bool)
      in
      ()
  in
  if (Core.Slice.impl__len #u8 pk1 <: usize) <. (impl_PublicKey1__len () <: usize)
  then
    pk1,
    (Core.Result.Result_Err (Error_InvalidOutputLength <: t_Error)
      <:
      Core.Result.t_Result Prims.unit t_Error)
    <:
    (t_Slice u8 & Core.Result.t_Result Prims.unit t_Error)
  else
    let pk1:t_Slice u8 =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_range pk1
        ({ Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 32 }
          <:
          Core.Ops.Range.t_Range usize)
        (Core.Slice.impl__copy_from_slice #u8
            (pk1.[ { Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 32 }
                <:
                Core.Ops.Range.t_Range usize ]
              <:
              t_Slice u8)
            (self.f_pk1.f_seed <: t_Slice u8)
          <:
          t_Slice u8)
    in
    let pk1:t_Slice u8 =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_range pk1
        ({ Core.Ops.Range.f_start = mk_usize 32; Core.Ops.Range.f_end = mk_usize 64 }
          <:
          Core.Ops.Range.t_Range usize)
        (Core.Slice.impl__copy_from_slice #u8
            (pk1.[ { Core.Ops.Range.f_start = mk_usize 32; Core.Ops.Range.f_end = mk_usize 64 }
                <:
                Core.Ops.Range.t_Range usize ]
              <:
              t_Slice u8)
            (self.f_pk1.f_hash <: t_Slice u8)
          <:
          t_Slice u8)
    in
    let hax_temp_output:Core.Result.t_Result Prims.unit t_Error =
      Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit t_Error
    in
    pk1, hax_temp_output <: (t_Slice u8 & Core.Result.t_Result Prims.unit t_Error)

let impl_15__pk2_bytes
      (v_K v_PK2_LEN: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self: t_KeyPair v_K v_PK2_LEN v_Vector)
      (pk2: t_Slice u8)
     =
  if (Core.Slice.impl__len #u8 pk2 <: usize) <. v_PK2_LEN
  then
    pk2,
    (Core.Result.Result_Err (Error_InvalidOutputLength <: t_Error)
      <:
      Core.Result.t_Result Prims.unit t_Error)
    <:
    (t_Slice u8 & Core.Result.t_Result Prims.unit t_Error)
  else
    let pk2:t_Slice u8 =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_range pk2
        ({ Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = v_PK2_LEN }
          <:
          Core.Ops.Range.t_Range usize)
        (Core.Slice.impl__copy_from_slice #u8
            (pk2.[ { Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = v_PK2_LEN }
                <:
                Core.Ops.Range.t_Range usize ]
              <:
              t_Slice u8)
            (self.f_pk2.f_tt_as_ntt <: t_Slice u8)
          <:
          t_Slice u8)
    in
    let hax_temp_output:Core.Result.t_Result Prims.unit t_Error =
      Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit t_Error
    in
    pk2, hax_temp_output <: (t_Slice u8 & Core.Result.t_Result Prims.unit t_Error)

let impl_15__num_bytes
      (v_K: usize)
      (v_PK2_LEN: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (_: Prims.unit)
     =
  ((((impl_PublicKey1__len () <: usize) +! (impl_4__len v_PK2_LEN () <: usize) <: usize) +!
      (Libcrux_ml_kem.Polynomial.vec_len_bytes v_K #v_Vector () <: usize)
      <:
      usize) +!
    mk_usize 32
    <:
    usize) +!
  (v_K *! (Libcrux_ml_kem.Polynomial.vec_len_bytes v_K #v_Vector () <: usize) <: usize)

let impl_15__from_bytes
      (v_K v_PK2_LEN: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (key: t_Slice u8)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 key <: usize) >=.
            (impl_15__num_bytes v_K v_PK2_LEN #v_Vector () <: usize)
            <:
            bool)
      in
      ()
  in
  if
    (Core.Slice.impl__len #u8 key <: usize) <.
    (impl_15__num_bytes v_K v_PK2_LEN #v_Vector () <: usize)
  then
    Core.Result.Result_Err (Error_InvalidInputLength <: t_Error)
    <:
    Core.Result.t_Result (t_KeyPair v_K v_PK2_LEN v_Vector) t_Error
  else
    match
      Core.Convert.f_try_from #t_PublicKey1 #(t_Slice u8) #FStar.Tactics.Typeclasses.solve key
      <:
      Core.Result.t_Result t_PublicKey1 t_Error
    with
    | Core.Result.Result_Ok pk1 ->
      let offset:usize = impl_PublicKey1__len () in
      (match
          Core.Convert.f_try_from #(t_PublicKey2 v_PK2_LEN)
            #(t_Slice u8)
            #FStar.Tactics.Typeclasses.solve
            (key.[ { Core.Ops.Range.f_start = offset } <: Core.Ops.Range.t_RangeFrom usize ]
              <:
              t_Slice u8)
          <:
          Core.Result.t_Result (t_PublicKey2 v_PK2_LEN) t_Error
        with
        | Core.Result.Result_Ok pk2 ->
          let offset:usize = offset +! (impl_4__len v_PK2_LEN () <: usize) in
          let implicit_rejection_value:t_Array u8 (mk_usize 32) =
            Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32)
          in
          let (sk: Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPrivateKeyUnpacked v_K v_Vector):Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPrivateKeyUnpacked
            v_K v_Vector =
            {
              Libcrux_ml_kem.Ind_cca.Unpacked.f_ind_cpa_private_key
              =
              Core.Default.f_default #(Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked
                    v_K v_Vector)
                #FStar.Tactics.Typeclasses.solve
                ();
              Libcrux_ml_kem.Ind_cca.Unpacked.f_implicit_rejection_value = implicit_rejection_value
            }
            <:
            Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPrivateKeyUnpacked v_K v_Vector
          in
          let sk:Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPrivateKeyUnpacked v_K v_Vector =
            {
              sk with
              Libcrux_ml_kem.Ind_cca.Unpacked.f_ind_cpa_private_key
              =
              {
                sk.Libcrux_ml_kem.Ind_cca.Unpacked.f_ind_cpa_private_key with
                Libcrux_ml_kem.Ind_cpa.Unpacked.f_secret_as_ntt
                =
                Libcrux_ml_kem.Polynomial.vec_from_bytes #v_Vector
                  (key.[ { Core.Ops.Range.f_start = offset } <: Core.Ops.Range.t_RangeFrom usize ]
                    <:
                    t_Slice u8)
                  sk.Libcrux_ml_kem.Ind_cca.Unpacked.f_ind_cpa_private_key
                    .Libcrux_ml_kem.Ind_cpa.Unpacked.f_secret_as_ntt
              }
              <:
              Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector
            }
            <:
            Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPrivateKeyUnpacked v_K v_Vector
          in
          let offset:usize =
            offset +! (Libcrux_ml_kem.Polynomial.vec_len_bytes v_K #v_Vector () <: usize)
          in
          let sk:Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPrivateKeyUnpacked v_K v_Vector =
            {
              sk with
              Libcrux_ml_kem.Ind_cca.Unpacked.f_implicit_rejection_value
              =
              Core.Slice.impl__copy_from_slice #u8
                sk.Libcrux_ml_kem.Ind_cca.Unpacked.f_implicit_rejection_value
                (key.[ {
                      Core.Ops.Range.f_start = offset;
                      Core.Ops.Range.f_end = offset +! mk_usize 32 <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
            }
            <:
            Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPrivateKeyUnpacked v_K v_Vector
          in
          let offset:usize =
            offset +!
            (Core.Slice.impl__len #u8
                (sk.Libcrux_ml_kem.Ind_cca.Unpacked.f_implicit_rejection_value <: t_Slice u8)
              <:
              usize)
          in
          let matrix:t_Array
            (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K =
            Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat (Libcrux_ml_kem.Polynomial.impl_2__ZERO
                      #v_Vector
                      ()
                    <:
                    Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                  v_K
                <:
                t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
              v_K
          in
          let matrix, offset:(t_Array
              (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K &
            usize) =
            Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
              (Core.Slice.impl__len #(t_Array
                      (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
                  (matrix
                    <:
                    t_Slice
                    (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K))
                <:
                usize)
              (fun temp_0_ temp_1_ ->
                  let matrix, offset:(t_Array
                      (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K &
                    usize) =
                    temp_0_
                  in
                  let _:usize = temp_1_ in
                  true)
              (matrix, offset
                <:
                (t_Array (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
                    v_K &
                  usize))
              (fun temp_0_ i ->
                  let matrix, offset:(t_Array
                      (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K &
                    usize) =
                    temp_0_
                  in
                  let i:usize = i in
                  let matrix:t_Array
                    (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize matrix
                      i
                      (Libcrux_ml_kem.Polynomial.vec_from_bytes #v_Vector
                          (key.[ { Core.Ops.Range.f_start = offset }
                              <:
                              Core.Ops.Range.t_RangeFrom usize ]
                            <:
                            t_Slice u8)
                          (matrix.[ i ]
                            <:
                            t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K
                          )
                        <:
                        t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
                  in
                  let offset:usize =
                    offset +! (Libcrux_ml_kem.Polynomial.vec_len_bytes v_K #v_Vector () <: usize)
                  in
                  matrix, offset
                  <:
                  (t_Array
                      (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K &
                    usize))
          in
          Core.Result.Result_Ok
          ({ f_pk1 = pk1; f_pk2 = pk2; f_sk = sk; f_matrix = matrix }
            <:
            t_KeyPair v_K v_PK2_LEN v_Vector)
          <:
          Core.Result.t_Result (t_KeyPair v_K v_PK2_LEN v_Vector) t_Error
        | Core.Result.Result_Err err ->
          Core.Result.Result_Err err
          <:
          Core.Result.t_Result (t_KeyPair v_K v_PK2_LEN v_Vector) t_Error)
    | Core.Result.Result_Err err ->
      Core.Result.Result_Err err <: Core.Result.t_Result (t_KeyPair v_K v_PK2_LEN v_Vector) t_Error

let impl_15__to_bytes__write (out value: t_Slice u8) (offset: usize) =
  let new_offset:usize = offset +! (Core.Slice.impl__len #u8 value <: usize) in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
      ({ Core.Ops.Range.f_start = offset; Core.Ops.Range.f_end = new_offset }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (out.[ { Core.Ops.Range.f_start = offset; Core.Ops.Range.f_end = new_offset }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          value
        <:
        t_Slice u8)
  in
  let offset:usize = new_offset in
  out, offset <: (t_Slice u8 & usize)

let impl_15__to_bytes
      (v_K v_PK2_LEN: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self: t_KeyPair v_K v_PK2_LEN v_Vector)
      (key: t_Slice u8)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 key <: usize) >=.
            (impl_15__num_bytes v_K v_PK2_LEN #v_Vector () <: usize)
            <:
            bool)
      in
      ()
  in
  if
    (Core.Slice.impl__len #u8 key <: usize) <.
    (impl_15__num_bytes v_K v_PK2_LEN #v_Vector () <: usize)
  then
    key,
    (Core.Result.Result_Err (Error_InvalidInputLength <: t_Error)
      <:
      Core.Result.t_Result Prims.unit t_Error)
    <:
    (t_Slice u8 & Core.Result.t_Result Prims.unit t_Error)
  else
    let offset:usize = mk_usize 0 in
    let tmp0, tmp1:(t_Slice u8 & usize) =
      impl_15__to_bytes__write key (self.f_pk1.f_seed <: t_Slice u8) offset
    in
    let key:t_Slice u8 = tmp0 in
    let offset:usize = tmp1 in
    let _:Prims.unit = () in
    let tmp0, tmp1:(t_Slice u8 & usize) =
      impl_15__to_bytes__write key (self.f_pk1.f_hash <: t_Slice u8) offset
    in
    let key:t_Slice u8 = tmp0 in
    let offset:usize = tmp1 in
    let _:Prims.unit = () in
    let tmp0, tmp1:(t_Slice u8 & usize) =
      impl_15__to_bytes__write key (self.f_pk2.f_tt_as_ntt <: t_Slice u8) offset
    in
    let key:t_Slice u8 = tmp0 in
    let offset:usize = tmp1 in
    let _:Prims.unit = () in
    let key:t_Slice u8 =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from key
        ({ Core.Ops.Range.f_start = offset } <: Core.Ops.Range.t_RangeFrom usize)
        (Libcrux_ml_kem.Polynomial.vec_to_bytes #v_Vector
            (self.f_sk.Libcrux_ml_kem.Ind_cca.Unpacked.f_ind_cpa_private_key
                .Libcrux_ml_kem.Ind_cpa.Unpacked.f_secret_as_ntt
              <:
              t_Slice (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
            (key.[ { Core.Ops.Range.f_start = offset } <: Core.Ops.Range.t_RangeFrom usize ]
              <:
              t_Slice u8)
          <:
          t_Slice u8)
    in
    let offset:usize =
      offset +! (Libcrux_ml_kem.Polynomial.vec_len_bytes v_K #v_Vector () <: usize)
    in
    let tmp0, tmp1:(t_Slice u8 & usize) =
      impl_15__to_bytes__write key
        (self.f_sk.Libcrux_ml_kem.Ind_cca.Unpacked.f_implicit_rejection_value <: t_Slice u8)
        offset
    in
    let key:t_Slice u8 = tmp0 in
    let offset:usize = tmp1 in
    let _:Prims.unit = () in
    let key, offset:(t_Slice u8 & usize) =
      Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
        (Core.Slice.impl__len #(t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                v_K)
            (self.f_matrix
              <:
              t_Slice (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K))
          <:
          usize)
        (fun temp_0_ temp_1_ ->
            let key, offset:(t_Slice u8 & usize) = temp_0_ in
            let _:usize = temp_1_ in
            true)
        (key, offset <: (t_Slice u8 & usize))
        (fun temp_0_ i ->
            let key, offset:(t_Slice u8 & usize) = temp_0_ in
            let i:usize = i in
            let key:t_Slice u8 =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from key
                ({ Core.Ops.Range.f_start = offset } <: Core.Ops.Range.t_RangeFrom usize)
                (Libcrux_ml_kem.Polynomial.vec_to_bytes #v_Vector
                    (self.f_matrix.[ i ]
                      <:
                      t_Slice (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
                    (key.[ { Core.Ops.Range.f_start = offset } <: Core.Ops.Range.t_RangeFrom usize ]
                      <:
                      t_Slice u8)
                  <:
                  t_Slice u8)
            in
            let offset:usize =
              offset +! (Libcrux_ml_kem.Polynomial.vec_len_bytes v_K #v_Vector () <: usize)
            in
            key, offset <: (t_Slice u8 & usize))
    in
    let hax_temp_output:Core.Result.t_Result Prims.unit t_Error =
      Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit t_Error
    in
    key, hax_temp_output <: (t_Slice u8 & Core.Result.t_Result Prims.unit t_Error)
