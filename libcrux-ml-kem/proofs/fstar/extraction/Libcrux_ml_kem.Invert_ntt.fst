module Libcrux_ml_kem.Invert_ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Vector.Traits in
  ()

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

let zetas_b_lemma (i:nat{i >= 0 /\ i < 128}) : Lemma
   (Spec.Utils.is_i16b 1664 (Libcrux_ml_kem.Polynomial.get_zeta (sz i))) =
   admit()

let invert_ntt_at_layer_1_
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (zeta_i: usize)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (v__layer: usize)
     =
  let v__zeta_i_init:usize = zeta_i in
  let re, zeta_i:(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (sz 16)
      (fun temp_0_ round ->
          let re, zeta_i:(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
            temp_0_
          in
          let round:usize = round in
          v zeta_i == v v__zeta_i_init - v round * 4)
      (re, zeta_i <: (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
            temp_0_
          in
          let round:usize = round in
          let zeta_i:usize = zeta_i -! sz 1 in
          let _:Prims.unit =
            zetas_b_lemma (v zeta_i);
            zetas_b_lemma (v zeta_i - 1);
            zetas_b_lemma (v zeta_i - 2);
            zetas_b_lemma (v zeta_i - 3)
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
                    (Libcrux_ml_kem.Polynomial.get_zeta zeta_i <: i16)
                    (Libcrux_ml_kem.Polynomial.get_zeta (zeta_i -! sz 1 <: usize) <: i16)
                    (Libcrux_ml_kem.Polynomial.get_zeta (zeta_i -! sz 2 <: usize) <: i16)
                    (Libcrux_ml_kem.Polynomial.get_zeta (zeta_i -! sz 3 <: usize) <: i16)
                  <:
                  v_Vector)
            }
            <:
            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
          in
          let zeta_i:usize = zeta_i -! sz 3 in
          re, zeta_i <: (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize))
  in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  zeta_i, re <: (usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)

let invert_ntt_at_layer_2_
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (zeta_i: usize)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (v__layer: usize)
     =
  let v__zeta_i_init:usize = zeta_i in
  let re, zeta_i:(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (sz 16)
      (fun temp_0_ round ->
          let re, zeta_i:(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
            temp_0_
          in
          let round:usize = round in
          v zeta_i == v v__zeta_i_init - v round * 2)
      (re, zeta_i <: (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
            temp_0_
          in
          let round:usize = round in
          let zeta_i:usize = zeta_i -! sz 1 in
          let _:Prims.unit =
            zetas_b_lemma (v zeta_i);
            zetas_b_lemma (v zeta_i - 1)
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
                    (Libcrux_ml_kem.Polynomial.get_zeta zeta_i <: i16)
                    (Libcrux_ml_kem.Polynomial.get_zeta (zeta_i -! sz 1 <: usize) <: i16)
                  <:
                  v_Vector)
            }
            <:
            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
          in
          let zeta_i:usize = zeta_i -! sz 1 in
          re, zeta_i <: (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize))
  in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  zeta_i, re <: (usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)

let invert_ntt_at_layer_3_
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (zeta_i: usize)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (v__layer: usize)
     =
  let v__zeta_i_init:usize = zeta_i in
  let re, zeta_i:(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (sz 16)
      (fun temp_0_ round ->
          let re, zeta_i:(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
            temp_0_
          in
          let round:usize = round in
          v zeta_i == v v__zeta_i_init - v round)
      (re, zeta_i <: (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
            temp_0_
          in
          let round:usize = round in
          let zeta_i:usize = zeta_i -! sz 1 in
          let _:Prims.unit = zetas_b_lemma (v zeta_i) in
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
                    (Libcrux_ml_kem.Polynomial.get_zeta zeta_i <: i16)
                  <:
                  v_Vector)
            }
            <:
            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
          in
          re, zeta_i <: (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize))
  in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  zeta_i, re <: (usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)

#push-options "--z3rlimit 2000"

let invert_ntt_at_layer_4_plus
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (zeta_i: usize)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (layer: usize)
     =
  assert (v layer == 4 \/ v layer == 5 \/ v layer == 6 \/ v layer == 7);
  assume (v layer == 4 ==> (forall i. i <= 14 ==> inv_ntt_reduce_condition
    re.f_coefficients.[ sz i ] re.f_coefficients.[ sz i +! sz 1 ]));
  assume (v layer == 5 ==> (forall i. i <= 13 ==> inv_ntt_reduce_condition
    re.f_coefficients.[ sz i ] re.f_coefficients.[ sz i +! sz 2 ]));
  assume (v layer == 6 ==> (forall i. i <= 11 ==> inv_ntt_reduce_condition
    re.f_coefficients.[ sz i ] re.f_coefficients.[ sz i +! sz 4 ]));
  assume (v layer == 7 ==> (forall i. i <= 7 ==> inv_ntt_reduce_condition
    re.f_coefficients.[ sz i ] re.f_coefficients.[ sz i +! sz 8 ]));
  let step:usize = sz 1 <<! layer in
  assert (1 * pow2 (v layer) == pow2 (v layer));
  Math.Lemmas.pow2_lt_compat 32 (v layer);
  Math.Lemmas.pow2_lt_compat 64 (v layer);
  Math.Lemmas.modulo_lemma (pow2 (v layer)) (pow2 32);
  Math.Lemmas.modulo_lemma (pow2 (v layer)) (pow2 64);
  assert (pow2 (v layer) % (modulus usize_inttype) == pow2 (v layer));
  assert ((v layer == 4 ==> v step == 16) /\
    (v layer == 5 ==> v step == 32) /\
    (v layer == 6 ==> v step == 64) /\
    (v layer == 7 ==> v step == 128));
  assert ((v layer == 4 ==> v (sz 128 >>! layer) == 8) /\
    (v layer == 5 ==> v (sz 128 >>! layer) == 4) /\
    (v layer == 6 ==> v (sz 128 >>! layer) == 2) /\
    (v layer == 7 ==> v (sz 128 >>! layer) == 1));
  let v__zeta_i_init:usize = zeta_i in
  let re, zeta_i:(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (sz 128 >>! layer <: usize)
      (fun temp_0_ round ->
          let re, zeta_i:(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
            temp_0_
          in
          let round:usize = round in
          v zeta_i == v v__zeta_i_init - v round)
      (re, zeta_i <: (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
            temp_0_
          in
          let round:usize = round in
          assert ((v layer == 4 ==> v round < 8) /\
            (v layer == 5 ==> v round < 4) /\
            (v layer == 6 ==> v round < 2) /\
            (v layer == 7 ==> v round < 1));
          assert ((v layer == 4 ==> v round == 0 \/ v round == 1 \/ v round == 2 \/ v round == 3 \/
              v round == 4 \/ v round == 5 \/ v round == 6 \/ v round == 7) /\
            (v layer == 5 ==> v round == 0 \/ v round == 1 \/ v round == 2 \/ v round == 3) /\
            (v layer == 6 ==> v round == 0 \/ v round == 1) /\
            (v layer == 7 ==> v round == 0));
          let _:Prims.unit =
            assert (v round < 8);
            assert (v step >= 16 /\ v step <= 128);
            assert (v (round *! step) >= 0 /\ v (round *! step) <= 112)
          in
          let zeta_i:usize = zeta_i -! sz 1 in
          let offset:usize = (round *! step <: usize) *! sz 2 in
          assert (v (round *! step) == v round * v step);
          assert (v offset == (v round * v step) * 2);
          assert ((v layer == 4 ==> v offset == 0 \/ v offset == 32 \/ v offset == 64 \/ v offset == 96 \/
              v offset == 128 \/ v offset == 160 \/ v offset == 192 \/ v offset == 224) /\
            (v layer == 5 ==> v offset == 0 \/ v offset == 64 \/ v offset == 128 \/ v offset == 192) /\
            (v layer == 6 ==> v offset == 0 \/ v offset == 128) /\
            (v layer == 7 ==> v offset == 0));
          // assert ((v layer == 4 ==> v offset < 256) /\
          //   (v layer == 5 ==> v offset < 4) /\
          //   (v layer == 6 ==> v offset < 2) /\
          //   (v layer == 7 ==> v offset < 1));
          //admit();
          let _:Prims.unit = assert (v offset >= 0 /\ v offset <= 224) in
          let offset_vec:usize =
            offset /! Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
          in
          assert (v offset_vec == v offset / v Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR);
          assert ((v layer == 4 ==> v offset_vec == 0 \/ v offset_vec == 2 \/ v offset_vec == 4 \/ v offset_vec == 6 \/
              v offset_vec == 8 \/ v offset_vec == 10 \/ v offset_vec == 12 \/ v offset_vec == 14) /\
            (v layer == 5 ==> v offset_vec == 0 \/ v offset_vec == 4 \/ v offset_vec == 8 \/ v offset_vec == 12) /\
            (v layer == 6 ==> v offset_vec == 0 \/ v offset_vec == 8) /\
            (v layer == 7 ==> v offset_vec == 0));
          let step_vec:usize = step /! Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR in
          assert (v step_vec == v step / v Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR);
          assert ((v layer == 4 ==> v step_vec == 1) /\
            (v layer == 5 ==> v step_vec == 2) /\
            (v layer == 6 ==> v step_vec == 4) /\
            (v layer == 7 ==> v step_vec == 8));
          assert (v (offset_vec +! step_vec) == v offset_vec + v step_vec);
          assert (v layer == 4 ==> (v offset_vec == 0 /\ v (offset_vec +! step_vec) == 1) \/
            (v offset_vec == 2 /\ v (offset_vec +! step_vec) == 3) \/
            (v offset_vec == 4 /\ v (offset_vec +! step_vec) == 5) \/
            (v offset_vec == 6 /\ v (offset_vec +! step_vec) == 7) \/
            (v offset_vec == 8 /\ v (offset_vec +! step_vec) == 9) \/
            (v offset_vec == 10 /\ v (offset_vec +! step_vec) == 11) \/
            (v offset_vec == 12 /\ v (offset_vec +! step_vec) == 13) \/
            (v offset_vec == 14 /\ v (offset_vec +! step_vec) == 15));
          assert (v layer == 5 ==> (v offset_vec == 0 /\ v (offset_vec +! step_vec) == 2) \/
            (v offset_vec == 4 /\ v (offset_vec +! step_vec) == 6) \/
            (v offset_vec == 8 /\ v (offset_vec +! step_vec) == 10) \/
            (v offset_vec == 12 /\ v (offset_vec +! step_vec) == 14));
          assert (v layer == 6 ==> (v offset_vec == 0 /\ v (offset_vec +! step_vec) == 4) \/
            (v offset_vec == 8 /\ v (offset_vec +! step_vec) == 12));
          assert (v layer == 7 ==> v offset_vec == 0 /\ v (offset_vec +! step_vec) == 8);
          //admit();
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
                  let _:Prims.unit = zetas_b_lemma (v zeta_i) in
                  //admit();
                  assert (v layer == 4 ==> (forall i. i <= 14 ==> inv_ntt_reduce_condition
                    re.f_coefficients.[ sz i ] re.f_coefficients.[ sz i +! sz 1 ]));
                  let _:Prims.unit =
                    assert (let a = re.f_coefficients.[ j ] in
                        let b = re.f_coefficients.[ j +! step_vec ] in
                        inv_ntt_reduce_condition
                                  a
                                  b)
                  in
                  admit();
                  let x, y:(v_Vector & v_Vector) =
                    inv_ntt_layer_int_vec_step_reduce #v_Vector
                      (re.Libcrux_ml_kem.Polynomial.f_coefficients.[ j ] <: v_Vector)
                      (re.Libcrux_ml_kem.Polynomial.f_coefficients.[ j +! step_vec <: usize ]
                        <:
                        v_Vector)
                      (Libcrux_ml_kem.Polynomial.get_zeta zeta_i <: i16)
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
  admit();
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  zeta_i, re <: (usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)

#pop-options

let invert_ntt_at_layer_4_plus

#push-options "--z3rlimit 200"

let invert_ntt_montgomery
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
     =
  let zeta_i:usize = Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT /! sz 2 in
  let tmp0, tmp1:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    invert_ntt_at_layer_1_ #v_Vector zeta_i re (sz 1)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    invert_ntt_at_layer_2_ #v_Vector zeta_i re (sz 2)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    invert_ntt_at_layer_3_ #v_Vector zeta_i re (sz 3)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    invert_ntt_at_layer_4_plus #v_Vector zeta_i re (sz 4)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    invert_ntt_at_layer_4_plus #v_Vector zeta_i re (sz 5)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    invert_ntt_at_layer_4_plus #v_Vector zeta_i re (sz 6)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    invert_ntt_at_layer_4_plus #v_Vector zeta_i re (sz 7)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let _:Prims.unit = () in
  let hax_temp_output, re:(Prims.unit & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
  =
    (), Libcrux_ml_kem.Polynomial.impl_2__poly_barrett_reduce #v_Vector re
    <:
    (Prims.unit & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
  in
  re

#pop-options
