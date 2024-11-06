module Libcrux_ml_dsa.Simd.Traits
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let montgomery_multiply_by_fer
      (#v_S: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Operations v_S)
      (simd_unit: v_S)
      (fer: i32)
     = f_montgomery_multiply_by_constant #v_S #FStar.Tactics.Typeclasses.solve simd_unit fer
