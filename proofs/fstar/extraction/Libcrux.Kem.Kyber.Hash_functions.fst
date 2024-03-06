module Libcrux.Kem.Kyber.Hash_functions
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_G (input: t_Slice u8) = Libcrux.Digest.sha3_512_ input

let v_H (input: t_Slice u8) = Libcrux.Digest.sha3_256_ input

let v_PRF (v_LEN: usize) (input: t_Slice u8) = Libcrux.Digest.shake256 v_LEN input

let v_XOF_absorb (v_K: usize) (input: t_Array (t_Array u8 (sz 34)) v_K) =
  let state:Libcrux.Digest.t_Shake128State v_K = Libcrux.Digest.shake128_init v_K () in
  let state:Libcrux.Digest.t_Shake128State v_K =
    Libcrux.Digest.shake128_absorb_final v_K state input
  in
  state

let v_XOF_free (v_K: usize) (xof_state: Libcrux.Digest.t_Shake128State v_K) =
  let xof_state:Libcrux.Digest.t_Shake128State v_K = Libcrux.Digest.impl_3__free v_K xof_state in
  ()

let v_XOF_squeeze_block (v_K: usize) (xof_state: Libcrux.Digest.t_Shake128State v_K) =
  let tmp0, out:(Libcrux.Digest.t_Shake128State v_K & t_Array (t_Array u8 (sz 168)) v_K) =
    Libcrux.Digest.shake128_squeeze_nblocks (sz 168) v_K xof_state
  in
  let xof_state:Libcrux.Digest.t_Shake128State v_K = tmp0 in
  let output:t_Array (t_Array u8 (sz 168)) v_K = out in
  output, xof_state <: (t_Array (t_Array u8 (sz 168)) v_K & Libcrux.Digest.t_Shake128State v_K)

let v_XOF_squeeze_three_blocks (v_K: usize) (xof_state: Libcrux.Digest.t_Shake128State v_K) =
  let tmp0, out:(Libcrux.Digest.t_Shake128State v_K & t_Array (t_Array u8 (sz 504)) v_K) =
    Libcrux.Digest.shake128_squeeze_nblocks (sz 504) v_K xof_state
  in
  let xof_state:Libcrux.Digest.t_Shake128State v_K = tmp0 in
  let output:t_Array (t_Array u8 (sz 504)) v_K = out in
  output, xof_state <: (t_Array (t_Array u8 (sz 504)) v_K & Libcrux.Digest.t_Shake128State v_K)
