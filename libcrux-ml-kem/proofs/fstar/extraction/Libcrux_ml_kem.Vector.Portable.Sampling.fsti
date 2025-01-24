module Libcrux_ml_kem.Vector.Portable.Sampling
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

val rej_sample (a: t_Slice u8) (result: t_Slice i16)
    : Prims.Pure (t_Slice i16 & usize)
      (requires
        (Core.Slice.impl__len #u8 a <: usize) =. mk_usize 24 &&
        (Core.Slice.impl__len #i16 result <: usize) =. mk_usize 16)
      (ensures
        fun temp_0_ ->
          let result_future, res:(t_Slice i16 & usize) = temp_0_ in
          Seq.length result_future == Seq.length result /\ v res <= 16)
