module Libcrux_ml_kem.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let invert_ntt_montgomery
      (v_K: usize)
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_traits.t_Operations v_Vector)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
     =
  let zeta_i:usize = Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT /! sz 2 in
  let tmp0, out:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    Libcrux_ml_kem.Polynomial.invert_ntt_at_layer_1_ zeta_i re (sz 1)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = out in
  let tmp0, out:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    Libcrux_ml_kem.Polynomial.invert_ntt_at_layer_2_ zeta_i re (sz 2)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = out in
  let tmp0, out:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    Libcrux_ml_kem.Polynomial.invert_ntt_at_layer_3_plus zeta_i re (sz 3)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = out in
  let tmp0, out:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    Libcrux_ml_kem.Polynomial.invert_ntt_at_layer_3_plus zeta_i re (sz 4)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = out in
  let tmp0, out:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    Libcrux_ml_kem.Polynomial.invert_ntt_at_layer_3_plus zeta_i re (sz 5)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = out in
  let tmp0, out:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    Libcrux_ml_kem.Polynomial.invert_ntt_at_layer_3_plus zeta_i re (sz 6)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = out in
  let tmp0, out:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    Libcrux_ml_kem.Polynomial.invert_ntt_at_layer_3_plus zeta_i re (sz 7)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = out in
  Libcrux_ml_kem.Polynomial.impl__poly_barrett_reduce re

let ntt_vector_u
      (v_VECTOR_U_COMPRESSION_FACTOR: usize)
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_traits.t_Operations v_Vector)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
     =
  let zeta_i:usize = sz 0 in
  let tmp0, out:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    Libcrux_ml_kem.Polynomial.ntt_at_layer_3_plus zeta_i re (sz 7) (sz 3328)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = out in
  let tmp0, out:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    Libcrux_ml_kem.Polynomial.ntt_at_layer_3_plus zeta_i re (sz 6) (sz 3328)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = out in
  let tmp0, out:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    Libcrux_ml_kem.Polynomial.ntt_at_layer_3_plus zeta_i re (sz 5) (sz 3328)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = out in
  let tmp0, out:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    Libcrux_ml_kem.Polynomial.ntt_at_layer_3_plus zeta_i re (sz 4) (sz 3328)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = out in
  let tmp0, out:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    Libcrux_ml_kem.Polynomial.ntt_at_layer_3_plus zeta_i re (sz 3) (sz 3328)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = out in
  let tmp0, out:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    Libcrux_ml_kem.Polynomial.ntt_at_layer_2_ zeta_i re (sz 2) (sz 3328)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = out in
  let tmp0, out:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    Libcrux_ml_kem.Polynomial.ntt_at_layer_1_ zeta_i re (sz 1) (sz 3328)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = out in
  Libcrux_ml_kem.Polynomial.impl__poly_barrett_reduce re

let ntt_binomially_sampled_ring_element
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_traits.t_Operations v_Vector)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
     =
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Polynomial.ntt_at_layer_7_ re
  in
  let zeta_i:usize = sz 1 in
  let tmp0, out:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    Libcrux_ml_kem.Polynomial.ntt_at_layer_3_plus zeta_i re (sz 6) (sz 3)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = out in
  let tmp0, out:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    Libcrux_ml_kem.Polynomial.ntt_at_layer_3_plus zeta_i re (sz 5) (sz 3)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = out in
  let tmp0, out:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    Libcrux_ml_kem.Polynomial.ntt_at_layer_3_plus zeta_i re (sz 4) (sz 3)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = out in
  let tmp0, out:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    Libcrux_ml_kem.Polynomial.ntt_at_layer_3_plus zeta_i re (sz 3) (sz 3)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = out in
  let tmp0, out:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    Libcrux_ml_kem.Polynomial.ntt_at_layer_2_ zeta_i re (sz 2) (sz 3)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = out in
  let tmp0, out:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    Libcrux_ml_kem.Polynomial.ntt_at_layer_1_ zeta_i re (sz 1) (sz 3)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = out in
  Libcrux_ml_kem.Polynomial.impl__poly_barrett_reduce re
