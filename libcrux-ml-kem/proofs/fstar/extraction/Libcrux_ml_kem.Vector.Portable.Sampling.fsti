module Libcrux_ml_kem.Vector.Portable.Sampling
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val rej_sample (a: t_Slice u8) (result: t_Slice i16)
    : Prims.Pure (t_Slice i16 & usize)
      (requires (Core.Slice.impl__len #u8 a <: usize) =. sz 24)
      (ensures
        fun temp_0_ ->
          let result_future, res:(t_Slice i16 & usize) = temp_0_ in
          Seq.length (future (result)) == Seq.length result)
