module Libcrux_ml_kem.Vector.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_PortableVector = { f_elements:t_Array i16 (sz 16) }

let t_BI16 (v_B: usize) =
  x:
  i16
    { x >. (Core.Ops.Arith.Neg.neg (cast (v_B <: usize) <: i16) <: i16) &&
      x <. (cast (v_B <: usize) <: i16) }
