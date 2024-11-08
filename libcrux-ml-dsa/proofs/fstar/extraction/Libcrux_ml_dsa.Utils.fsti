module Libcrux_ml_dsa.Utils
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

/// Pad the `slice` with `0`s at the end.
val into_padded_array (v_LEN: usize) (slice: t_Slice u8)
    : Prims.Pure (t_Array u8 v_LEN) Prims.l_True (fun _ -> Prims.l_True)
