module Libcrux_ml_kem.Vector.Traits
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let to_standard_domain
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Operations v_T)
      (v: v_T)
     =
  f_montgomery_multiply_by_constant #v_T
    #FStar.Tactics.Typeclasses.solve
    v
    v_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS

#push-options "--admit_smt_queries true"

let to_unsigned_representative
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Operations v_T)
      (a: v_T)
     =
  let t:v_T = f_shift_right #v_T #FStar.Tactics.Typeclasses.solve (mk_i32 15) a in
  let fm:v_T =
    f_bitwise_and_with_constant #v_T #FStar.Tactics.Typeclasses.solve t v_FIELD_MODULUS
  in
  f_add #v_T #FStar.Tactics.Typeclasses.solve a fm

#pop-options
