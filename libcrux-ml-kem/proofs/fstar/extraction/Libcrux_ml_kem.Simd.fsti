module Libcrux_ml_kem.Simd
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

unfold
let t_Vector = Libcrux_ml_kem.Simd.Simd256.t_SIMD256Vector
