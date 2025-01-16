module Libcrux_ml_dsa.Samplex4.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Hash_functions.Portable in
  let open Libcrux_ml_dsa.Hash_functions.Shake128 in
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Libcrux_ml_dsa.Samplex4.t_X4Sampler t_PortableSampler =
  {
    f_matrix_flat_pre
    =
    (fun
        (#v_SIMDUnit: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
        (columns: usize)
        (seed: t_Slice u8)
        (matrix: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
        ->
        true);
    f_matrix_flat_post
    =
    (fun
        (#v_SIMDUnit: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
        (columns: usize)
        (seed: t_Slice u8)
        (matrix: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
        (out: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
        ->
        true);
    f_matrix_flat
    =
    fun
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
        i1:
        Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (columns: usize)
      (seed: t_Slice u8)
      (matrix: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      ->
      let matrix:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
        Libcrux_ml_dsa.Samplex4.matrix_flat #v_SIMDUnit
          #Libcrux_ml_dsa.Hash_functions.Portable.t_Shake128X4
          columns
          seed
          matrix
      in
      matrix
  }
