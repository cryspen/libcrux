module Libcrux.Kem.Kyber.Hash_functions
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_BLOCK_SIZE: usize = sz 168

val v_G (input: t_Slice u8) : Prims.Pure (t_Array u8 (sz 64)) Prims.l_True (fun _ -> Prims.l_True)

val v_H (input: t_Slice u8) : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

val v_PRF (v_LEN: usize) (input: t_Slice u8)
    : Prims.Pure (t_Array u8 v_LEN) Prims.l_True (fun _ -> Prims.l_True)

let v_THREE_BLOCKS: usize = v_BLOCK_SIZE *! sz 3

type t_Shake128State (v_K: usize) = {
  f_state:t_Array Libcrux.Hacl.Sha3.Incremental.t_Shake128State v_K
}

val impl__new: v_K: usize -> Prims.unit
  -> Prims.Pure (t_Shake128State v_K) Prims.l_True (fun _ -> Prims.l_True)

val absorb (v_K: usize) (input: t_Array (t_Array u8 (sz 34)) v_K)
    : Prims.Pure (t_Shake128State v_K) Prims.l_True (fun _ -> Prims.l_True)

val free (v_K: usize) (xof_state: t_Shake128State v_K)
    : Prims.Pure (t_Shake128State v_K) Prims.l_True (fun _ -> Prims.l_True)

val squeeze_block (v_K: usize) (xof_state: t_Shake128State v_K)
    : Prims.Pure (t_Shake128State v_K & t_Array (t_Array u8 (sz 168)) v_K)
      Prims.l_True
      (fun _ -> Prims.l_True)

val squeeze_three_blocks (v_K: usize) (xof_state: t_Shake128State v_K)
    : Prims.Pure (t_Shake128State v_K & t_Array (t_Array u8 (sz 504)) v_K)
      Prims.l_True
      (fun _ -> Prims.l_True)
