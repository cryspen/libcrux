module Libcrux_ml_kem.Invert_ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Vector.Traits in
  ()

[@@ "opaque_to_smt"]
let inv_ntt_reduce_condition (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (a b: v_Vector) =
    (forall i. i < 16 ==>
        Spec.Utils.is_intb (pow2 15 - 1)
        (v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array b) i) -
        v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array a) i))) /\
    (forall i. i < 16 ==>
        Spec.Utils.is_intb (pow2 15 - 1)
        (v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array a) i) +
        v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array b) i))) /\
    Spec.Utils.is_i16b_array 28296 (Libcrux_ml_kem.Vector.Traits.f_to_i16_array
        (Libcrux_ml_kem.Vector.Traits.f_add a b))

val inv_ntt_layer_int_vec_step_reduce
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (a b: v_Vector)
      (zeta_r: i16)
    : Prims.Pure (v_Vector & v_Vector)
      (requires Spec.Utils.is_i16b 1664 zeta_r /\ inv_ntt_reduce_condition a b)
      (fun _ -> Prims.l_True)

val invert_ntt_at_layer_1_
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (zeta_i: usize)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (v__layer: usize)
    : Prims.Pure (usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires v zeta_i >= 64 && v zeta_i <= 128)
      (fun _ -> Prims.l_True)

val invert_ntt_at_layer_2_
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (zeta_i: usize)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (v__layer: usize)
    : Prims.Pure (usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires v zeta_i >= 32 && v zeta_i <= 128)
      (fun _ -> Prims.l_True)

val invert_ntt_at_layer_3_
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (zeta_i: usize)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (v__layer: usize)
    : Prims.Pure (usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires v zeta_i >= 16 && v zeta_i <= 128)
      (fun _ -> Prims.l_True)

val invert_ntt_at_layer_4_plus
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (zeta_i: usize)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (layer: usize)
    : Prims.Pure (usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires
        v layer >= 4 /\ v layer <= 7 /\ v zeta_i - v (sz 128 >>! layer) >= 0 /\ v zeta_i <= 128)
      (fun _ -> Prims.l_True)

val invert_ntt_montgomery
      (v_K: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
    : Prims.Pure (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      Prims.l_True
      (fun _ -> Prims.l_True)
