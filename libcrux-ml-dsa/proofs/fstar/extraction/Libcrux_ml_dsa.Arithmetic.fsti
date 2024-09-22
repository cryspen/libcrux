module Libcrux_ml_dsa.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

val decompose_vector
      (#v_SIMDUnit: Type0)
      (v_DIMENSION: usize)
      (v_GAMMA2: i32)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (t: t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION)
    : Prims.Pure
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION &
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION)
      Prims.l_True
      (fun _ -> Prims.l_True)

val power2round_vector
      (#v_SIMDUnit: Type0)
      (v_DIMENSION: usize)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (t: t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION)
    : Prims.Pure
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION &
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION)
      Prims.l_True
      (fun _ -> Prims.l_True)

val shift_left_then_reduce
      (#v_SIMDUnit: Type0)
      (v_SHIFT_BY: i32)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    : Prims.Pure (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      Prims.l_True
      (fun _ -> Prims.l_True)

val use_hint
      (#v_SIMDUnit: Type0)
      (v_DIMENSION: usize)
      (v_GAMMA2: i32)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (hint: t_Array (t_Array i32 (sz 256)) v_DIMENSION)
      (re_vector: t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION
        )
    : Prims.Pure
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION)
      Prims.l_True
      (fun _ -> Prims.l_True)

val vector_infinity_norm_exceeds
      (#v_SIMDUnit: Type0)
      (v_DIMENSION: usize)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (vector: t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION)
      (bound: i32)
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

val make_hint
      (#v_SIMDUnit: Type0)
      (v_DIMENSION: usize)
      (v_GAMMA2: i32)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (low high: t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION)
    : Prims.Pure (t_Array (t_Array i32 (sz 256)) v_DIMENSION & usize)
      Prims.l_True
      (fun _ -> Prims.l_True)
