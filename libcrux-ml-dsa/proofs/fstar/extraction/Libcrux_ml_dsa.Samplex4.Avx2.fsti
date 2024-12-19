module Libcrux_ml_dsa.Samplex4.Avx2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Hash_functions.Shake128 in
  let open Libcrux_ml_dsa.Hash_functions.Simd256 in
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

type t_AVX2Sampler = | AVX2Sampler : t_AVX2Sampler

val matrix_A_avx2
      (#v_SIMDUnit: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A: usize)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (seed: t_Array u8 (sz 34))
    : Prims.Pure
      (t_Array
          (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          v_ROWS_IN_A) Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl:Libcrux_ml_dsa.Samplex4.t_X4Sampler t_AVX2Sampler
