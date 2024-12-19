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

let matrix_A_avx2
      (#v_SIMDUnit: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (seed: t_Array u8 (sz 34))
     =
  match
    (cast (v_ROWS_IN_A <: usize) <: u8), (cast (v_COLUMNS_IN_A <: usize) <: u8) <: (u8 & u8)
  with
  | 4uy, 4uy ->
    Libcrux_ml_dsa.Samplex4.matrix_A_4_by_4_ #v_SIMDUnit
      #Libcrux_ml_dsa.Hash_functions.Simd256.t_Shake128x4
      v_ROWS_IN_A
      v_COLUMNS_IN_A
      seed
  | 6uy, 5uy ->
    Libcrux_ml_dsa.Samplex4.matrix_A_6_by_5_ #v_SIMDUnit
      #Libcrux_ml_dsa.Hash_functions.Simd256.t_Shake128x4
      v_ROWS_IN_A
      v_COLUMNS_IN_A
      seed
  | 8uy, 7uy ->
    Libcrux_ml_dsa.Samplex4.matrix_A_8_by_7_ #v_SIMDUnit
      #Libcrux_ml_dsa.Hash_functions.Simd256.t_Shake128x4
      v_ROWS_IN_A
      v_COLUMNS_IN_A
      seed
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Libcrux_ml_dsa.Samplex4.t_X4Sampler t_AVX2Sampler =
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
      matrix_A_avx2 #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A seed
  }
