module Libcrux_sha3.Avx2.X4
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// Perform 4 SHAKE256 operations in parallel
val shake256
      (v_LEN: usize)
      (input0 input1 input2 input3: t_Slice u8)
      (out: t_Array (t_Array u8 v_LEN) (sz 4))
    : Prims.Pure (t_Array (t_Array u8 v_LEN) (sz 4)) Prims.l_True (fun _ -> Prims.l_True)
