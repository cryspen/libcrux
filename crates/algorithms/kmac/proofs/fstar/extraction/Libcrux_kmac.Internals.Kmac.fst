module Libcrux_kmac.Internals.Kmac
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_sha3.Portable.Incremental in
  ()

let v_KMAC_LABEL: t_Array u8 (mk_usize 4) =
  let list = [mk_u8 75; mk_u8 77; mk_u8 65; mk_u8 67] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
  Rust_primitives.Hax.array_of_list 4 list

let compute_kmac
      (v_RATE: usize)
      (#v_CShakeState: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_sha3.Portable.Incremental.t_CShake v_CShakeState v_RATE)
      (tag: t_Slice u8)
      (tag_length: usize)
      (key: t_Slice u8)
      (key_length: usize)
      (data customization: t_Slice u8)
    : Prims.Pure (t_Slice u8 & t_Slice u8)
      (requires v_RATE =. mk_usize 136 || v_RATE =. mk_usize 168)
      (fun _ -> Prims.l_True) =
  let state:v_CShakeState =
    Libcrux_sha3.Portable.Incremental.f_new_cshake #v_CShakeState
      #v_RATE
      #FStar.Tactics.Typeclasses.solve
      (v_KMAC_LABEL <: t_Slice u8)
      customization
  in
  let zeros:t_Array u8 v_RATE = Rust_primitives.Hax.repeat (mk_u8 0) v_RATE in
  let key_bits:usize = key_length <<! mk_i32 3 in
  let tag_bits:usize = tag_length <<! mk_i32 3 in
  let b:t_Array u8 (mk_usize 9) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 9) in
  let state:v_CShakeState =
    Libcrux_sha3.Portable.Incremental.f_absorb_cshake #v_CShakeState
      #v_RATE
      #FStar.Tactics.Typeclasses.solve
      state
      (Libcrux_sha3.Portable.Incremental.Cshake.left_encode_byte (cast (v_RATE <: usize) <: u8)
        <:
        t_Slice u8)
  in
  let (tmp0: t_Array u8 (mk_usize 9)), (out: t_Slice u8) =
    Libcrux_sha3.Portable.Incremental.Cshake.left_encode key_bits b
  in
  let b:t_Array u8 (mk_usize 9) = tmp0 in
  let key_enc:t_Slice u8 = out in
  let state:v_CShakeState =
    Libcrux_sha3.Portable.Incremental.f_absorb_cshake #v_CShakeState
      #v_RATE
      #FStar.Tactics.Typeclasses.solve
      state
      key_enc
  in
  let state:v_CShakeState =
    Libcrux_sha3.Portable.Incremental.f_absorb_cshake #v_CShakeState
      #v_RATE
      #FStar.Tactics.Typeclasses.solve
      state
      key
  in
  let buffer_len:usize =
    (mk_usize 2 +! (Core_models.Slice.impl__len #u8 key_enc <: usize) <: usize) +!
    (key_length %! v_RATE <: usize)
  in
  let n_zeros:usize = (v_RATE -! (buffer_len %! v_RATE <: usize) <: usize) %! v_RATE in
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit = Hax_lib.v_assert (n_zeros <. v_RATE <: bool) in
      ()
  in
  let state:v_CShakeState =
    Libcrux_sha3.Portable.Incremental.f_absorb_cshake #v_CShakeState
      #v_RATE
      #FStar.Tactics.Typeclasses.solve
      state
      (zeros.[ { Core_models.Ops.Range.f_end = n_zeros } <: Core_models.Ops.Range.t_RangeTo usize ]
        <:
        t_Slice u8)
  in
  let state:v_CShakeState =
    Libcrux_sha3.Portable.Incremental.f_absorb_cshake #v_CShakeState
      #v_RATE
      #FStar.Tactics.Typeclasses.solve
      state
      data
  in
  let (tmp0: t_Array u8 (mk_usize 9)), (out: t_Slice u8) =
    Libcrux_sha3.Portable.Incremental.Cshake.right_encode tag_bits b
  in
  let b:t_Array u8 (mk_usize 9) = tmp0 in
  let state:v_CShakeState =
    Libcrux_sha3.Portable.Incremental.f_absorb_final_cshake #v_CShakeState
      #v_RATE
      #FStar.Tactics.Typeclasses.solve
      state
      out
  in
  let (tmp0: v_CShakeState), (tmp1: t_Slice u8) =
    Libcrux_sha3.Portable.Incremental.f_squeeze_cshake #v_CShakeState
      #v_RATE
      #FStar.Tactics.Typeclasses.solve
      state
      tag
  in
  let state:v_CShakeState = tmp0 in
  let tag:t_Slice u8 = tmp1 in
  let _:Prims.unit = () in
  let hax_temp_output:t_Slice u8 = tag in
  tag, hax_temp_output <: (t_Slice u8 & t_Slice u8)
