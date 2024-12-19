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
    f_matrix_A_pre
    =
    (fun
        (#v_SIMDUnit: Type0)
        (v_ROWS_IN_A: usize)
        (v_COLUMNS_IN_A: usize)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
        (seed: t_Array u8 (sz 34))
        ->
        true);
    f_matrix_A_post
    =
    (fun
        (#v_SIMDUnit: Type0)
        (v_ROWS_IN_A: usize)
        (v_COLUMNS_IN_A: usize)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
        (seed: t_Array u8 (sz 34))
        (out:
          t_Array
            (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
            v_ROWS_IN_A)
        ->
        true);
    f_matrix_A
    =
    fun
      (#v_SIMDUnit: Type0)
      (v_ROWS_IN_A: usize)
      (v_COLUMNS_IN_A: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
        i1:
        Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (seed: t_Array u8 (sz 34))
      ->
      Libcrux_ml_dsa.Samplex4.matrix_A_generic #v_SIMDUnit
        #Libcrux_ml_dsa.Hash_functions.Portable.t_Shake128X4
        v_ROWS_IN_A
        v_COLUMNS_IN_A
        seed
  }
