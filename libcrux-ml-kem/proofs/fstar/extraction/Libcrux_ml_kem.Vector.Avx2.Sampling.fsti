module Libcrux_ml_kem.Vector.Avx2.Sampling
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val rejection_sample (input: t_Slice u8) (output: t_Slice i16)
    : Prims.Pure (t_Slice i16 & usize) Prims.l_True (fun _ -> Prims.l_True)
