module Libcrux.Kem.Kyber.Hash_functions
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val v_G (input: t_Slice u8) : Prims.Pure (t_Array u8 (sz 64)) Prims.l_True (fun _ -> Prims.l_True)

val v_H (input: t_Slice u8) : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

val v_PRF (v_LEN: usize) (input: t_Slice u8)
    : Prims.Pure (t_Array u8 v_LEN) Prims.l_True (fun _ -> Prims.l_True)

type t_XofState =
  | XofState_X2 : Libcrux.Digest.t_Shake128StateX2 -> t_XofState
  | XofState_X3 : Libcrux.Digest.t_Shake128StateX3 -> t_XofState
  | XofState_X4 : Libcrux.Digest.t_Shake128StateX4 -> t_XofState

val v_XOF_absorb (v_K: usize) (input: t_Array (t_Array u8 (sz 34)) v_K)
    : Prims.Pure t_XofState Prims.l_True (fun _ -> Prims.l_True)

val v_XOF_free (v_K: usize) (xof_state: t_XofState)
    : Prims.Pure Prims.unit Prims.l_True (fun _ -> Prims.l_True)

val v_XOF_squeeze_block (v_K: usize) (xof_state: t_XofState)
    : Prims.Pure (t_Array (t_Array u8 (sz 168)) v_K & t_XofState)
      Prims.l_True
      (fun _ -> Prims.l_True)

val v_XOF_squeeze_three_blocks (v_K: usize) (xof_state: t_XofState)
    : Prims.Pure (t_Array (t_Array u8 (sz 504)) v_K & t_XofState)
      Prims.l_True
      (fun _ -> Prims.l_True)
