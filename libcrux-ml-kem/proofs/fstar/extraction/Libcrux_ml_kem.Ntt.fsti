module Libcrux_ml_kem.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Vector.Traits in
  ()

val ntt_layer_int_vec_step
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (a b: v_Vector)
      (zeta_r: i16)
    : Prims.Pure (v_Vector & v_Vector)
      (requires
        Spec.Utils.is_i16b 1664 zeta_r /\
        (let t = Libcrux_ml_kem.Vector.Traits.montgomery_multiply_fe b zeta_r in
          (forall (i: nat).
              i < 16 ==>
              Spec.Utils.is_intb (pow2 15 - 1)
                (v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array a) i) -
                  v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array t) i))) /\
          (forall (i: nat).
              i < 16 ==>
              Spec.Utils.is_intb (pow2 15 - 1)
                (v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array a) i) +
                  v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array t) i)))))
      (fun _ -> Prims.l_True)

[@@ "opaque_to_smt"]
    let ntt_re_range_1 (#v_Vector: Type0)
            {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
            (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
        forall (i:nat). i < 16 ==> Spec.Utils.is_i16b_array_opaque (11207+6*3328)
                (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ]))

[@@ "opaque_to_smt"]
   let ntt_re_range_2 (#v_Vector: Type0)
         {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
         (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
       forall (i:nat). i < 16 ==> Spec.Utils.is_i16b_array_opaque (11207+5*3328)
            (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ]))

val ntt_at_layer_1_
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (zeta_i: usize)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (v__layer v__initial_coefficient_bound: usize)
    : Prims.Pure (usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires v zeta_i == 63 /\ ntt_re_range_2 re)
      (ensures
        fun temp_0_ ->
          let zeta_i_future, re_future:(usize &
            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
            temp_0_
          in
          ntt_re_range_1 re_future /\ v zeta_i_future == 127)

[@@ "opaque_to_smt"]
   let ntt_re_range_3 (#v_Vector: Type0)
         {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
         (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
       forall (i:nat). i < 16 ==> Spec.Utils.is_i16b_array_opaque (11207+4*3328)
            (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ]))

val ntt_at_layer_2_
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (zeta_i: usize)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (v__layer v__initial_coefficient_bound: usize)
    : Prims.Pure (usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires v zeta_i == 31 /\ ntt_re_range_3 re)
      (ensures
        fun temp_0_ ->
          let zeta_i_future, re_future:(usize &
            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
            temp_0_
          in
          ntt_re_range_2 re_future /\ v zeta_i_future == 63)

[@@ "opaque_to_smt"]
   let ntt_re_range_4 (#v_Vector: Type0)
         {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
         (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
       forall (i:nat). i < 16 ==> Spec.Utils.is_i16b_array_opaque (11207+3*3328)
            (Libcrux_ml_kem.Vector.Traits.f_to_i16_array (re.f_coefficients.[ sz i ]))

val ntt_at_layer_3_
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (zeta_i: usize)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (v__layer v__initial_coefficient_bound: usize)
    : Prims.Pure (usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires v zeta_i == 15 /\ ntt_re_range_4 re)
      (ensures
        fun temp_0_ ->
          let zeta_i_future, re_future:(usize &
            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
            temp_0_
          in
          ntt_re_range_3 re_future /\ v zeta_i_future == 31)

val ntt_at_layer_4_plus
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (zeta_i: usize)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (layer v__initial_coefficient_bound: usize)
    : Prims.Pure (usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires
        v layer >= 4 /\ v layer <= 7 /\
        ((v layer == 4 ==> v zeta_i == 7) /\ (v layer == 5 ==> v zeta_i == 3) /\
          (v layer == 6 ==> v zeta_i == 1) /\ (v layer == 7 ==> v zeta_i == 0)))
      (ensures
        fun temp_0_ ->
          let zeta_i_future, re_future:(usize &
            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
            temp_0_
          in
          ntt_re_range_4 re_future /\ (v layer == 4 ==> v zeta_i_future == 15) /\
          (v layer == 5 ==> v zeta_i_future == 7) /\ (v layer == 6 ==> v zeta_i_future == 3) /\
          (v layer == 7 ==> v zeta_i_future == 1))

[@@ "opaque_to_smt"]
   let ntt_layer_7_pre (#v_Vector: Type0)
        {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
        (re_0 re_1: v_Vector) =
    (forall (i:nat). i < 16 ==>
      Spec.Utils.is_intb (pow2 15 - 1)
      (v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array re_1) i) * v (-1600s))) /\
    (let t = Libcrux_ml_kem.Vector.Traits.f_multiply_by_constant re_1 (-1600s) in
    (forall (i:nat). i < 16 ==> 
      Spec.Utils.is_intb (pow2 15 - 1) 
        (v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array re_0) i) - 
          v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array t) i))) /\
    (forall (i:nat). i < 16 ==> 
      Spec.Utils.is_intb (pow2 15 - 1) 
        (v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array re_0) i) + 
          v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array t) i))))

val ntt_at_layer_7_
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
    : Prims.Pure (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires
        forall (i: nat).
          i < 8 ==>
          ntt_layer_7_pre (re.f_coefficients.[ sz i ]) (re.f_coefficients.[ sz i +! sz 8 ]))
      (fun _ -> Prims.l_True)

val ntt_binomially_sampled_ring_element
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
    : Prims.Pure (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires
        forall (i: nat).
          i < 8 ==>
          ntt_layer_7_pre (re.f_coefficients.[ sz i ]) (re.f_coefficients.[ sz i +! sz 8 ]))
      (fun _ -> Prims.l_True)

val ntt_vector_u
      (v_VECTOR_U_COMPRESSION_FACTOR: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
    : Prims.Pure (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      Prims.l_True
      (fun _ -> Prims.l_True)
