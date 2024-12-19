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
  f_matrix_A_pre:
      #v_SIMDUnit: Type0 ->
      v_ROWS_IN_A: usize ->
      v_COLUMNS_IN_A: usize ->
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |} ->
      t_Array u8 (sz 34)
    -> Type0;
  f_matrix_A_post:
      #v_SIMDUnit: Type0 ->
      v_ROWS_IN_A: usize ->
      v_COLUMNS_IN_A: usize ->
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |} ->
      t_Array u8 (sz 34) ->
      t_Array
          (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          v_ROWS_IN_A
    -> Type0;
  f_matrix_A:
      #v_SIMDUnit: Type0 ->
      v_ROWS_IN_A: usize ->
      v_COLUMNS_IN_A: usize ->
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |} ->
      x0: t_Array u8 (sz 34)
    -> Prims.Pure
        (t_Array
            (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
            v_ROWS_IN_A)
        (f_matrix_A_pre #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A #i1 x0)
        (fun result -> f_matrix_A_post #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A #i1 x0 result)
}

val matrix_A_4_by_4_
      (#v_SIMDUnit #v_Shake128: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A: usize)
      {| i2: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i3: Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128 |}
      (seed: t_Array u8 (sz 34))
    : Prims.Pure
      (t_Array
          (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          v_ROWS_IN_A) Prims.l_True (fun _ -> Prims.l_True)

val matrix_A_6_by_5_
      (#v_SIMDUnit #v_Shake128: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A: usize)
      {| i2: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i3: Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128 |}
      (seed: t_Array u8 (sz 34))
    : Prims.Pure
      (t_Array
          (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          v_ROWS_IN_A) Prims.l_True (fun _ -> Prims.l_True)

val matrix_A_8_by_7_
      (#v_SIMDUnit #v_Shake128: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A: usize)
      {| i2: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i3: Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128 |}
      (seed: t_Array u8 (sz 34))
    : Prims.Pure
      (t_Array
          (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          v_ROWS_IN_A) Prims.l_True (fun _ -> Prims.l_True)

val matrix_A_generic
      (#v_SIMDUnit #v_Shake128: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A: usize)
      {| i2: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i3: Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128 |}
      (seed: t_Array u8 (sz 34))
    : Prims.Pure
      (t_Array
          (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          v_ROWS_IN_A) Prims.l_True (fun _ -> Prims.l_True)

val sample_s1_and_s2_4_by_4_
      (#v_SIMDUnit #v_Shake256X4: Type0)
      (v_ETA v_S1_DIMENSION v_S2_DIMENSION: usize)
      {| i2: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i3: Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4 |}
      (seed_base: t_Array u8 (sz 66))
    : Prims.Pure
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION &
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION)
      Prims.l_True
      (fun _ -> Prims.l_True)

val sample_s1_and_s2_5_by_6_
      (#v_SIMDUnit #v_Shake256X4: Type0)
      (v_ETA v_S1_DIMENSION v_S2_DIMENSION: usize)
      {| i2: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i3: Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4 |}
      (seed_base: t_Array u8 (sz 66))
    : Prims.Pure
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION &
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION)
      Prims.l_True
      (fun _ -> Prims.l_True)

val sample_s1_and_s2_7_by_8_
      (#v_SIMDUnit #v_Shake256X4: Type0)
      (v_ETA v_S1_DIMENSION v_S2_DIMENSION: usize)
      {| i2: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i3: Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4 |}
      (seed_base: t_Array u8 (sz 66))
    : Prims.Pure
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION &
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION)
      Prims.l_True
      (fun _ -> Prims.l_True)

val sample_s1_and_s2
      (#v_SIMDUnit #v_Shake256X4: Type0)
      (v_ETA v_S1_DIMENSION v_S2_DIMENSION: usize)
      {| i2: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i3: Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4 |}
      (seed: t_Array u8 (sz 66))
    : Prims.Pure
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION &
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION)
      Prims.l_True
      (fun _ -> Prims.l_True)
