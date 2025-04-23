module BitVecEq

open Core
open FStar.Mul
open FStar.FunctionalExtensionality

let bit_vec_equal #n bv1 bv2 = forall i. bv1 i == bv2 i

let bit_vec_equal_intro bv1 bv2 = ()
let bit_vec_equal_elim bv1 bv2 = assert (feq bv1 bv2)


