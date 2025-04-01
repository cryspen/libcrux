module Libcrux_ml_kem.Vector.Traits.Spec
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let add_pre (lhs rhs: t_Array i16 (mk_usize 16)) : Hax_lib.Prop.t_Prop =
  forall i. i < 16 ==> Spec.Utils.is_intb (pow2 15 - 1) (v (Seq.index lhs i) + v (Seq.index rhs i))

let add_post (lhs rhs result: t_Array i16 (mk_usize 16)) : Hax_lib.Prop.t_Prop =
  forall i. i < 16 ==> (v (Seq.index result i) == v (Seq.index lhs i) + v (Seq.index rhs i))
