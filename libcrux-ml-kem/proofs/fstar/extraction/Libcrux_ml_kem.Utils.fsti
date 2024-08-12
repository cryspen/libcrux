module Libcrux_ml_kem.Utils
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// Pad the `slice` with `0`s at the end.
val into_padded_array (v_LEN: usize) (slice: t_Slice u8)
    : Prims.Pure (t_Array u8 v_LEN)
      (requires (Core.Slice.impl__len #u8 slice <: usize) <=. v_LEN)
      (ensures
        fun res ->
          let res:t_Array u8 v_LEN = res in
          Seq.slice res 0 (Seq.length slice) == slice)
