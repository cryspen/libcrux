module Libcrux_ml_kem.Vector.Avx2.Sampling
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

val rejection_sample (input: t_Slice u8) (output: t_Slice i16)
    : Prims.Pure (t_Slice i16 & usize)
      (requires
        (Core.Slice.impl__len #u8 input <: usize) =. mk_usize 24 &&
        (Core.Slice.impl__len #i16 output <: usize) =. mk_usize 16)
      (ensures
        fun temp_0_ ->
          let output_future, res:(t_Slice i16 & usize) = temp_0_ in
          Seq.length output_future == Seq.length output /\ v res <= 16)
