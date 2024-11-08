module Libcrux_ml_kem.Vector.Traits
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

#push-options "--z3rlimit 200 --split_queries always"

let decompress_1_
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Operations v_T)
      (vec: v_T)
     =
  let z:v_T = f_ZERO #v_T #FStar.Tactics.Typeclasses.solve () in
  let _:Prims.unit =
    assert (forall i. Seq.index (i1._super_8706949974463268012.f_repr z) i == 0s)
  in
  let _:Prims.unit =
    assert (forall i.
          let x = Seq.index (i1._super_8706949974463268012.f_repr vec) i in
          ((0 - v x) == 0 \/ (0 - v x) == - 1))
  in
  let _:Prims.unit =
    assert (forall i.
          i < 16 ==>
          Spec.Utils.is_intb (pow2 15 - 1)
            (0 - v (Seq.index (i1._super_8706949974463268012.f_repr vec) i)))
  in
  let s:v_T = f_sub #v_T #FStar.Tactics.Typeclasses.solve z vec in
  let _:Prims.unit =
    assert (forall i.
          Seq.index (i1._super_8706949974463268012.f_repr s) i == 0s \/
          Seq.index (i1._super_8706949974463268012.f_repr s) i == (-1s))
  in
  let _:Prims.unit = assert (i1.f_bitwise_and_with_constant_pre s 1665s) in
  f_bitwise_and_with_constant #v_T #FStar.Tactics.Typeclasses.solve s 1665s

#pop-options

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

#push-options "--admit_smt_queries true"

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

#pop-options
