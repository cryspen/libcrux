module Libcrux_sha3.Neon.X2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// Run up to 4 SHAKE256 operations in parallel.
/// **PANICS** when `N` is not 2, 3, or 4.
val v__shake256xN (v_LEN v_N: usize) (input: t_Array (t_Array u8 (sz 33)) v_N)
    : Prims.Pure (t_Array (t_Array u8 v_LEN) v_N) Prims.l_True (fun _ -> Prims.l_True)

/// Run SHAKE256 on both inputs in parallel.
/// Writes the two results into `out0` and `out1`
val shake256 (input0 input1 out0 out1: t_Slice u8)
    : Prims.Pure (t_Slice u8 & t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)
