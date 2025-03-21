module Libcrux_ml_kem.Invert_ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Vector.Traits in
  ()

#push-options "--z3rlimit 200 --ext context_pruning"

let invert_ntt_at_layer_1_
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (zeta_i: usize)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
     =
  let _:Prims.unit = reveal_opaque (`%invert_ntt_re_range_1) (invert_ntt_re_range_1 #v_Vector) in
  let _:Prims.unit = reveal_opaque (`%invert_ntt_re_range_2) (invert_ntt_re_range_2 #v_Vector) in
  let e_zeta_i_init:usize = zeta_i in
  let re, zeta_i:(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 16)
      (fun temp_0_ round ->
          let re, zeta_i:(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
            temp_0_
          in
          let round:usize = round in
          v zeta_i == v e_zeta_i_init - v round * 4 /\
          (v round < 16 ==>
            (forall (i: nat).
                (i >= v round /\ i < 16) ==>
                Spec.Utils.is_i16b_array_opaque (4 * 3328)
                  (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ])))) /\
          (forall (i: nat).
              i < v round ==>
              Spec.Utils.is_i16b_array_opaque 3328
                (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ]))))
      (re, zeta_i <: (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
            temp_0_
          in
          let round:usize = round in
          let zeta_i:usize = zeta_i -! mk_usize 1 in
          let _:Prims.unit =
            reveal_opaque (`%Spec.Utils.is_i16b_array_opaque)
              (Spec.Utils.is_i16b_array_opaque (4 * 3328)
                  (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ round ])))
          in
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            {
              re with
              Libcrux_ml_kem.Polynomial.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_ml_kem.Polynomial.f_coefficients
                round
                (Libcrux_ml_kem.Vector.Traits.f_inv_ntt_layer_1_step #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (re.Libcrux_ml_kem.Polynomial.f_coefficients.[ round ] <: v_Vector)
                    (Libcrux_ml_kem.Polynomial.zeta zeta_i <: i16)
                    (Libcrux_ml_kem.Polynomial.zeta (zeta_i -! mk_usize 1 <: usize) <: i16)
                    (Libcrux_ml_kem.Polynomial.zeta (zeta_i -! mk_usize 2 <: usize) <: i16)
                    (Libcrux_ml_kem.Polynomial.zeta (zeta_i -! mk_usize 3 <: usize) <: i16)
                  <:
                  v_Vector)
            }
            <:
            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
          in
          let zeta_i:usize = zeta_i -! mk_usize 3 in
          let _:Prims.unit =
            reveal_opaque (`%Spec.Utils.is_i16b_array_opaque)
              (Spec.Utils.is_i16b_array_opaque 3328
                  (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ round ])))
          in
          let _:Prims.unit =
            assert (Spec.Utils.is_i16b_array_opaque 3328
                  (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ round ])))
          in
          re, zeta_i <: (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize))
  in
  zeta_i, re <: (usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)

#pop-options

#push-options "--z3rlimit 200 --ext context_pruning"

let invert_ntt_at_layer_2_
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (zeta_i: usize)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
     =
  let _:Prims.unit = reveal_opaque (`%invert_ntt_re_range_2) (invert_ntt_re_range_2 #v_Vector) in
  let e_zeta_i_init:usize = zeta_i in
  let re, zeta_i:(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 16)
      (fun temp_0_ round ->
          let re, zeta_i:(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
            temp_0_
          in
          let round:usize = round in
          v zeta_i == v e_zeta_i_init - v round * 2 /\
          (v round < 16 ==>
            (forall (i: nat).
                (i >= v round /\ i < 16) ==>
                Spec.Utils.is_i16b_array_opaque 3328
                  (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ])))) /\
          (forall (i: nat).
              i < v round ==>
              Spec.Utils.is_i16b_array_opaque 3328
                (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ]))))
      (re, zeta_i <: (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
            temp_0_
          in
          let round:usize = round in
          let zeta_i:usize = zeta_i -! mk_usize 1 in
          let _:Prims.unit =
            reveal_opaque (`%Spec.Utils.is_i16b_array_opaque)
              (Spec.Utils.is_i16b_array_opaque 3328
                  (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ round ])))
          in
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            {
              re with
              Libcrux_ml_kem.Polynomial.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_ml_kem.Polynomial.f_coefficients
                round
                (Libcrux_ml_kem.Vector.Traits.f_inv_ntt_layer_2_step #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (re.Libcrux_ml_kem.Polynomial.f_coefficients.[ round ] <: v_Vector)
                    (Libcrux_ml_kem.Polynomial.zeta zeta_i <: i16)
                    (Libcrux_ml_kem.Polynomial.zeta (zeta_i -! mk_usize 1 <: usize) <: i16)
                  <:
                  v_Vector)
            }
            <:
            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
          in
          let zeta_i:usize = zeta_i -! mk_usize 1 in
          let _:Prims.unit =
            reveal_opaque (`%Spec.Utils.is_i16b_array_opaque)
              (Spec.Utils.is_i16b_array_opaque 3328
                  (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ round ])))
          in
          let _:Prims.unit =
            assert (Spec.Utils.is_i16b_array_opaque 3328
                  (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ round ])))
          in
          re, zeta_i <: (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize))
  in
  zeta_i, re <: (usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)

#pop-options

#push-options "--z3rlimit 200 --ext context_pruning"

let invert_ntt_at_layer_3_
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (zeta_i: usize)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
     =
  let _:Prims.unit = reveal_opaque (`%invert_ntt_re_range_2) (invert_ntt_re_range_2 #v_Vector) in
  let e_zeta_i_init:usize = zeta_i in
  let re, zeta_i:(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 16)
      (fun temp_0_ round ->
          let re, zeta_i:(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
            temp_0_
          in
          let round:usize = round in
          v zeta_i == v e_zeta_i_init - v round /\
          (v round < 16 ==>
            (forall (i: nat).
                (i >= v round /\ i < 16) ==>
                Spec.Utils.is_i16b_array_opaque 3328
                  (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ])))) /\
          (forall (i: nat).
              i < v round ==>
              Spec.Utils.is_i16b_array_opaque 3328
                (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ]))))
      (re, zeta_i <: (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
            temp_0_
          in
          let round:usize = round in
          let zeta_i:usize = zeta_i -! mk_usize 1 in
          let _:Prims.unit =
            reveal_opaque (`%Spec.Utils.is_i16b_array_opaque)
              (Spec.Utils.is_i16b_array_opaque 3328
                  (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ round ])))
          in
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            {
              re with
              Libcrux_ml_kem.Polynomial.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_ml_kem.Polynomial.f_coefficients
                round
                (Libcrux_ml_kem.Vector.Traits.f_inv_ntt_layer_3_step #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (re.Libcrux_ml_kem.Polynomial.f_coefficients.[ round ] <: v_Vector)
                    (Libcrux_ml_kem.Polynomial.zeta zeta_i <: i16)
                  <:
                  v_Vector)
            }
            <:
            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
          in
          let _:Prims.unit =
            reveal_opaque (`%Spec.Utils.is_i16b_array_opaque)
              (Spec.Utils.is_i16b_array_opaque 3328
                  (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ round ])))
          in
          let _:Prims.unit =
            assert (Spec.Utils.is_i16b_array_opaque 3328
                  (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ round ])))
          in
          re, zeta_i <: (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize))
  in
  zeta_i, re <: (usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)

#pop-options

let inv_ntt_layer_int_vec_step_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (a b: v_Vector)
      (zeta_r: i16)
     =
  let a_minus_b:v_Vector =
    Libcrux_ml_kem.Vector.Traits.f_sub #v_Vector #FStar.Tactics.Typeclasses.solve b a
  in
  let a:v_Vector =
    Libcrux_ml_kem.Vector.Traits.f_barrett_reduce #v_Vector
      #FStar.Tactics.Typeclasses.solve
      (Libcrux_ml_kem.Vector.Traits.f_add #v_Vector #FStar.Tactics.Typeclasses.solve a b <: v_Vector
      )
  in
  let b:v_Vector = Libcrux_ml_kem.Vector.Traits.montgomery_multiply_fe #v_Vector a_minus_b zeta_r in
  a, b <: (v_Vector & v_Vector)

#push-options "--admit_smt_queries true"

let invert_ntt_at_layer_4_plus
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (zeta_i: usize)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (layer: usize)
     =
  let step:usize = mk_usize 1 <<! layer in
  let re, zeta_i:(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 128 >>! layer <: usize)
      (fun temp_0_ temp_1_ ->
          let re, zeta_i:(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (re, zeta_i <: (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
            temp_0_
          in
          let round:usize = round in
          let zeta_i:usize = zeta_i -! mk_usize 1 in
          let offset:usize = (round *! step <: usize) *! mk_usize 2 in
          let offset_vec:usize =
            offset /! Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
          in
          let step_vec:usize = step /! Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR in
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            Rust_primitives.Hax.Folds.fold_range offset_vec
              (offset_vec +! step_vec <: usize)
              (fun re temp_1_ ->
                  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = re in
                  let _:usize = temp_1_ in
                  true)
              re
              (fun re j ->
                  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = re in
                  let j:usize = j in
                  let x, y:(v_Vector & v_Vector) =
                    inv_ntt_layer_int_vec_step_reduce #v_Vector
                      (re.Libcrux_ml_kem.Polynomial.f_coefficients.[ j ] <: v_Vector)
                      (re.Libcrux_ml_kem.Polynomial.f_coefficients.[ j +! step_vec <: usize ]
                        <:
                        v_Vector)
                      (Libcrux_ml_kem.Polynomial.zeta zeta_i <: i16)
                  in
                  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
                    {
                      re with
                      Libcrux_ml_kem.Polynomial.f_coefficients
                      =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                          .Libcrux_ml_kem.Polynomial.f_coefficients
                        j
                        x
                    }
                    <:
                    Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
                  in
                  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
                    {
                      re with
                      Libcrux_ml_kem.Polynomial.f_coefficients
                      =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                          .Libcrux_ml_kem.Polynomial.f_coefficients
                        (j +! step_vec <: usize)
                        y
                    }
                    <:
                    Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
                  in
                  re)
          in
          re, zeta_i <: (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize))
  in
  zeta_i, re <: (usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)

#pop-options

let invert_ntt_montgomery
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
     =
  let zeta_i:usize = Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT /! mk_usize 2 in
  let tmp0, tmp1:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    invert_ntt_at_layer_1_ #v_Vector zeta_i re
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    invert_ntt_at_layer_2_ #v_Vector zeta_i re
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    invert_ntt_at_layer_3_ #v_Vector zeta_i re
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    invert_ntt_at_layer_4_plus #v_Vector zeta_i re (mk_usize 4)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    invert_ntt_at_layer_4_plus #v_Vector zeta_i re (mk_usize 5)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    invert_ntt_at_layer_4_plus #v_Vector zeta_i re (mk_usize 6)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    invert_ntt_at_layer_4_plus #v_Vector zeta_i re (mk_usize 7)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let _:Prims.unit = () in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Polynomial.impl_2__poly_barrett_reduce #v_Vector re
  in
  re
