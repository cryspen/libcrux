module Libcrux_ml_dsa.Samplex4
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Hash_functions.Shake128 in
  let open Libcrux_ml_dsa.Hash_functions.Shake256 in
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

/// The x4 sampling implementation that is selected during multiplexing.
class t_X4Sampler (v_Self: Type0) = {
  f_matrix_flat_pre:
      #v_SIMDUnit: Type0 ->
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |} ->
      usize ->
      t_Slice u8 ->
      t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    -> Type0;
  f_matrix_flat_post:
      #v_SIMDUnit: Type0 ->
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |} ->
      usize ->
      t_Slice u8 ->
      t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) ->
      t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    -> Type0;
  f_matrix_flat:
      #v_SIMDUnit: Type0 ->
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |} ->
      x0: usize ->
      x1: t_Slice u8 ->
      x2: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    -> Prims.Pure (t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
        (f_matrix_flat_pre #v_SIMDUnit #i1 x0 x1 x2)
        (fun result -> f_matrix_flat_post #v_SIMDUnit #i1 x0 x1 x2 result)
}

val matrix_flat
      (#v_SIMDUnit #v_Shake128: Type0)
      {| i2: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i3: Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128 |}
      (columns: usize)
      (seed: t_Slice u8)
      (matrix: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
    : Prims.Pure (t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      Prims.l_True
      (fun _ -> Prims.l_True)

val sample_s1_and_s2
      (#v_SIMDUnit #v_Shake256X4: Type0)
      {| i2: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i3: Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4 |}
      (eta: Libcrux_ml_dsa.Constants.t_Eta)
      (seed: t_Slice u8)
      (s1_s2: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
    : Prims.Pure (t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      Prims.l_True
      (fun _ -> Prims.l_True)
