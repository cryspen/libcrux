module Libcrux_ml_dsa.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

val vector_infinity_norm_exceeds
      (#v_SIMDUnit: Type0)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (vector: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (bound: i32)
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

val shift_left_then_reduce
      (#v_SIMDUnit: Type0)
      (v_SHIFT_BY: i32)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    : Prims.Pure (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      Prims.l_True
      (fun _ -> Prims.l_True)

val power2round_vector
      (#v_SIMDUnit: Type0)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (t t1: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
    : Prims.Pure
      (t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) &
        t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      Prims.l_True
      (fun _ -> Prims.l_True)

val decompose_vector
      (#v_SIMDUnit: Type0)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (dimension: usize)
      (gamma2: i32)
      (t low high: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
    : Prims.Pure
      (t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) &
        t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      Prims.l_True
      (fun _ -> Prims.l_True)

val make_hint
      (#v_SIMDUnit: Type0)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (low high: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (gamma2: i32)
      (hint: t_Slice (t_Array i32 (mk_usize 256)))
    : Prims.Pure (t_Slice (t_Array i32 (mk_usize 256)) & usize) Prims.l_True (fun _ -> Prims.l_True)

val use_hint
      (#v_SIMDUnit: Type0)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (gamma2: i32)
      (hint: t_Slice (t_Array i32 (mk_usize 256)))
      (re_vector: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
    : Prims.Pure (t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      Prims.l_True
      (fun _ -> Prims.l_True)
