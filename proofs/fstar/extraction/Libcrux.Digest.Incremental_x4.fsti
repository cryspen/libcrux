module Libcrux.Digest.Incremental_x4
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val t_Shake128StateX4:Type

val impl__Shake128StateX4__absorb_final
      (v_N: usize)
      (self: t_Shake128StateX4)
      (input: t_Array (t_Slice u8) v_N)
    : Prims.Pure t_Shake128StateX4 Prims.l_True (fun _ -> Prims.l_True)

val impl__Shake128StateX4__free (self: t_Shake128StateX4)
    : Prims.Pure Prims.unit Prims.l_True (fun _ -> Prims.l_True)

val impl__Shake128StateX4__new: Prims.unit
  -> Prims.Pure t_Shake128StateX4 Prims.l_True (fun _ -> Prims.l_True)

val impl__Shake128StateX4__squeeze_blocks (v_N v_M: usize) (self: t_Shake128StateX4)
    : Prims.Pure (t_Shake128StateX4 & t_Array (t_Array u8 v_N) v_M)
      Prims.l_True
      (fun _ -> Prims.l_True)
