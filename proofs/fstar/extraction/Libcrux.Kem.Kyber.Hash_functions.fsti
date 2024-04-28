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

val absorb (v_K: usize) (input: t_Array (t_Array u8 (sz 34)) v_K)
    : Prims.Pure Libcrux.Digest.Incremental_x4.t_Shake128StateX4
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Free the memory of the state.
/// **NOTE:** That this needs to be done manually for now.
val free_state (xof_state: Libcrux.Digest.Incremental_x4.t_Shake128StateX4)
    : Prims.Pure Prims.unit Prims.l_True (fun _ -> Prims.l_True)

val squeeze_block (v_K: usize) (xof_state: Libcrux.Digest.Incremental_x4.t_Shake128StateX4)
    : Prims.Pure
      (Libcrux.Digest.Incremental_x4.t_Shake128StateX4 & t_Array (t_Array u8 (sz 168)) v_K)
      Prims.l_True
      (fun _ -> Prims.l_True)

val squeeze_three_blocks (v_K: usize) (xof_state: Libcrux.Digest.Incremental_x4.t_Shake128StateX4)
    : Prims.Pure
      (Libcrux.Digest.Incremental_x4.t_Shake128StateX4 & t_Array (t_Array u8 (sz 504)) v_K)
      Prims.l_True
      (fun _ -> Prims.l_True)
