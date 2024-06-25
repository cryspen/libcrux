module Libcrux_sha3.Neon.X2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// Run SHAKE256 on both inputs in parallel.
/// Writes the two results into `out0` and `out1`
val shake256 (v_LEN: usize) (input0 input1: t_Slice u8) (out: t_Array (t_Array u8 v_LEN) (sz 2))
    : Prims.Pure (t_Array (t_Array u8 v_LEN) (sz 2)) Prims.l_True (fun _ -> Prims.l_True)
