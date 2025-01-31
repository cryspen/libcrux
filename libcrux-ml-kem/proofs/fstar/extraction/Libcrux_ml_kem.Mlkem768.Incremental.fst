module Libcrux_ml_kem.Mlkem768.Incremental
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Ind_cca.Incremental.Types in
  ()

let pk1_len (_: Prims.unit) = Libcrux_ml_kem.Ind_cca.Incremental.Types.impl_PublicKey1__len ()

let pk2_len (_: Prims.unit) = Libcrux_ml_kem.Mlkem768.v_RANKED_BYTES_PER_RING_ELEMENT

let key_pair_len (_: Prims.unit) =
  ((((pk1_len () <: usize) +! (pk2_len () <: usize) <: usize) +!
      ((Libcrux_ml_kem.Mlkem768.v_RANK *! mk_usize 16 <: usize) *! mk_usize 32 <: usize)
      <:
      usize) +!
    mk_usize 32
    <:
    usize) +!
  (((Libcrux_ml_kem.Mlkem768.v_RANK *! Libcrux_ml_kem.Mlkem768.v_RANK <: usize) *! mk_usize 16
      <:
      usize) *!
    mk_usize 32
    <:
    usize)

let encaps_state_len (_: Prims.unit) =
  (((Libcrux_ml_kem.Mlkem768.v_RANK *! mk_usize 16 <: usize) *! mk_usize 32 <: usize) +!
    (mk_usize 16 *! mk_usize 32 <: usize)
    <:
    usize) +!
  mk_usize 32

let generate_key_pair (randomness: t_Array u8 (mk_usize 64)) (key_pair: t_Slice u8) =
  let tmp0, out:(t_Slice u8 &
    Core.Result.t_Result Prims.unit Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error) =
    Libcrux_ml_kem.Ind_cca.Incremental.Multiplexing.generate_keypair (mk_usize 3) (mk_usize 1152)
      (mk_usize 1152) (mk_usize 2400) (mk_usize 1184) (mk_usize 1152) (mk_usize 2) (mk_usize 128)
      randomness key_pair
  in
  let key_pair:t_Slice u8 = tmp0 in
  let hax_temp_output:Core.Result.t_Result Prims.unit
    Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error =
    out
  in
  key_pair, hax_temp_output
  <:
  (t_Slice u8 & Core.Result.t_Result Prims.unit Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error)

let validate_pk (pk1: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_PublicKey1) (pk2: t_Slice u8) =
  Libcrux_ml_kem.Ind_cca.Incremental.Multiplexing.validate_pk (mk_usize 3) (mk_usize 1184) pk1 pk2

let encapsulate1
      (pk1: t_Slice u8)
      (randomness: t_Array u8 (mk_usize 32))
      (state shared_secret: t_Slice u8)
     =
  match
    Core.Convert.f_try_from #Libcrux_ml_kem.Ind_cca.Incremental.Types.t_PublicKey1
      #(t_Slice u8)
      #FStar.Tactics.Typeclasses.solve
      pk1
    <:
    Core.Result.t_Result Libcrux_ml_kem.Ind_cca.Incremental.Types.t_PublicKey1
      Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error
  with
  | Core.Result.Result_Ok public_key_part ->
    let tmp0, tmp1, out:(t_Slice u8 & t_Slice u8 &
      Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 (mk_usize 960))
        Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error) =
      Libcrux_ml_kem.Ind_cca.Incremental.Multiplexing.encapsulate1 (mk_usize 3) (mk_usize 1088)
        (mk_usize 960) (mk_usize 10) (mk_usize 320) (mk_usize 2) (mk_usize 128) (mk_usize 2)
        (mk_usize 128) public_key_part randomness state shared_secret
    in
    let state:t_Slice u8 = tmp0 in
    let shared_secret:t_Slice u8 = tmp1 in
    let hax_temp_output:Core.Result.t_Result
      (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 (mk_usize 960))
      Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error =
      out
    in
    state, shared_secret, hax_temp_output
    <:
    (t_Slice u8 & t_Slice u8 &
      Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 (mk_usize 960))
        Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error)
  | Core.Result.Result_Err err ->
    state,
    shared_secret,
    (Core.Result.Result_Err err
      <:
      Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 (mk_usize 960))
        Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error)
    <:
    (t_Slice u8 & t_Slice u8 &
      Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 (mk_usize 960))
        Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error)

let encapsulate2 (state public_key_part: t_Slice u8) =
  Libcrux_ml_kem.Ind_cca.Incremental.Multiplexing.encapsulate2 (mk_usize 3)
    (mk_usize 1152)
    (mk_usize 128)
    (mk_usize 4)
    state
    public_key_part

let decapsulate_incremental_key
      (private_key: t_Slice u8)
      (ciphertext1: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 (mk_usize 960))
      (ciphertext2: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext2 (mk_usize 128))
     =
  Libcrux_ml_kem.Ind_cca.Incremental.Multiplexing.decapsulate (mk_usize 3) (mk_usize 1152)
    (mk_usize 2400) (mk_usize 1152) (mk_usize 1184) (mk_usize 1088) (mk_usize 1152) (mk_usize 960)
    (mk_usize 128) (mk_usize 10) (mk_usize 4) (mk_usize 320) (mk_usize 2) (mk_usize 128)
    (mk_usize 2) (mk_usize 128) (mk_usize 1120) private_key ciphertext1 ciphertext2
