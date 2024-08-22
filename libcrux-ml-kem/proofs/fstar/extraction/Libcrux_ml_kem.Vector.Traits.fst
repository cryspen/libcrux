module Libcrux_ml_kem.Vector.Traits
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let decompress_1_
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Operations v_T)
      (v: v_T)
     =
  f_bitwise_and_with_constant #v_T
    #FStar.Tactics.Typeclasses.solve
    (f_sub #v_T
        #FStar.Tactics.Typeclasses.solve
        (f_ZERO #v_T #FStar.Tactics.Typeclasses.solve () <: v_T)
        v
      <:
      v_T)
    1665s

let montgomery_multiply_fe
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Operations v_T)
      (v: v_T)
      (fer: i16)
     = f_montgomery_multiply_by_constant #v_T #FStar.Tactics.Typeclasses.solve v fer

let to_standard_domain
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Operations v_T)
      (v: v_T)
     =
  f_montgomery_multiply_by_constant #v_T
    #FStar.Tactics.Typeclasses.solve
    v
    v_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS

let to_unsigned_representative
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Operations v_T)
      (a: v_T)
     =
  let t:v_T = f_shift_right #v_T #FStar.Tactics.Typeclasses.solve 15l a in
  let fm:v_T =
    f_bitwise_and_with_constant #v_T #FStar.Tactics.Typeclasses.solve t v_FIELD_MODULUS
  in
  f_add #v_T #FStar.Tactics.Typeclasses.solve a fm
