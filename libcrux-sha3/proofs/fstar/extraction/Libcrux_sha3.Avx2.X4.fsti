module Libcrux_sha3.Avx2.X4
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// Run up to 4 SHAKE256 operations in parallel.
/// **PANICS** when `N` is not 2, 3, or 4.
val v__shake256xN (v_LEN v_N: usize) (input: t_Array (t_Array u8 (sz 33)) v_N)
    : Prims.Pure (t_Array (t_Array u8 v_LEN) v_N) Prims.l_True (fun _ -> Prims.l_True)

/// Perform 4 SHAKE256 operations in parallel
val shake256 (input0 input1 input2 input3 out0 out1 out2 out3: t_Slice u8)
    : Prims.Pure (t_Slice u8 & t_Slice u8 & t_Slice u8 & t_Slice u8)
      Prims.l_True
      (fun _ -> Prims.l_True)
