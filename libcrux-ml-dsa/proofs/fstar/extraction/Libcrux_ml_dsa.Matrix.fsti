module Libcrux_ml_dsa.Matrix
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

val vector_times_ring_element
      (#v_SIMDUnit: Type0)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (vector: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (ring_element: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    : Prims.Pure (t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      Prims.l_True
      (fun _ -> Prims.l_True)

val add_vectors
      (#v_SIMDUnit: Type0)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (dimension: usize)
      (lhs rhs: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
    : Prims.Pure (t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Compute InvertNTT(Â ◦ ŝ₁) + s₂
val compute_as1_plus_s2
      (#v_SIMDUnit: Type0)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (rows_in_a columns_in_a: usize)
      (a_as_ntt s1_ntt s1_s2 result:
          t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
    : Prims.Pure (t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Compute InvertNTT(Â ◦ ŷ)
val compute_matrix_x_mask
      (#v_SIMDUnit: Type0)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (rows_in_a columns_in_a: usize)
      (matrix mask result: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
    : Prims.Pure (t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      Prims.l_True
      (fun _ -> Prims.l_True)

val subtract_vectors
      (#v_SIMDUnit: Type0)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (dimension: usize)
      (lhs rhs: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
    : Prims.Pure (t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Compute InvertNTT(Â ◦ ẑ - ĉ ◦ NTT(t₁2ᵈ))
val compute_w_approx
      (#v_SIMDUnit: Type0)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (rows_in_a columns_in_a: usize)
      (matrix signer_response:
          t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (verifier_challenge_as_ntt: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      (t1: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
    : Prims.Pure (t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      Prims.l_True
      (fun _ -> Prims.l_True)
