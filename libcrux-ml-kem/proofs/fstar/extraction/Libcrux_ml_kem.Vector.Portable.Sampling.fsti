module Libcrux_ml_kem.Vector.Portable.Sampling
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val rej_sample (a: t_Slice u8) (result: t_Slice i16)
    : Prims.Pure (t_Slice i16 & usize) Prims.l_True (fun _ -> Prims.l_True)
