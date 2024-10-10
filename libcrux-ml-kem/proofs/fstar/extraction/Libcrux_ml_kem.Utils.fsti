module Libcrux_ml_kem.Utils
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

/// Pad the `slice` with `0`s at the end.
val into_padded_array (v_LEN: usize) (slice: t_Slice u8)
    : Prims.Pure (t_Array u8 v_LEN)
      (requires (Core.Slice.impl__len #u8 slice <: usize) <=. v_LEN)
      (ensures
        fun result ->
          let result:t_Array u8 v_LEN = result in
          result ==
          Seq.append slice (Seq.create (v v_LEN - v (Core.Slice.impl__len #u8 slice)) (mk_u8 0)))
