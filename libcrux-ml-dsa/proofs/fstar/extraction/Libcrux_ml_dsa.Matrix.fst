module Libcrux_ml_dsa.Matrix
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

let vector_times_ring_element
      (#v_SIMDUnit: Type0)
      (v_DIMENSION: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (vector: t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION)
      (ring_element: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
     =
  let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__ZERO #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      v_DIMENSION
  in
  let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION =
    Rust_primitives.Hax.Folds.fold_enumerated_slice (vector
        <:
        t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (fun result temp_1_ ->
          let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_DIMENSION =
            result
          in
          let _:usize = temp_1_ in
          true)
      result
      (fun result temp_1_ ->
          let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_DIMENSION =
            result
          in
          let i, vector_ring_element:(usize &
            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
            temp_1_
          in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
            i
            (Libcrux_ml_dsa.Ntt.invert_ntt_montgomery #v_SIMDUnit
                (Libcrux_ml_dsa.Ntt.ntt_multiply_montgomery #v_SIMDUnit
                    vector_ring_element
                    ring_element
                  <:
                  Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
              <:
              Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          <:
          t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION)
  in
  result

let add_vectors
      (#v_SIMDUnit: Type0)
      (v_DIMENSION: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (lhs rhs: t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION)
     =
  let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__ZERO #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      v_DIMENSION
  in
  let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      v_DIMENSION
      (fun result temp_1_ ->
          let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_DIMENSION =
            result
          in
          let _:usize = temp_1_ in
          true)
      result
      (fun result i ->
          let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_DIMENSION =
            result
          in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
            i
            (Libcrux_ml_dsa.Polynomial.impl__add #v_SIMDUnit
                (lhs.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                (rhs.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
              <:
              Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          <:
          t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION)
  in
  result

let compute_A_times_mask
      (#v_SIMDUnit: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (v_A_as_ntt:
          t_Array
            (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
            v_ROWS_IN_A)
      (mask: t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
     =
  let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__ZERO #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      v_ROWS_IN_A
  in
  let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A =
    Rust_primitives.Hax.Folds.fold_enumerated_slice (v_A_as_ntt
        <:
        t_Slice
        (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A))
      (fun result temp_1_ ->
          let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_ROWS_IN_A =
            result
          in
          let _:usize = temp_1_ in
          true)
      result
      (fun result temp_1_ ->
          let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_ROWS_IN_A =
            result
          in
          let i, row:(usize &
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A) =
            temp_1_
          in
          let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_ROWS_IN_A =
            Rust_primitives.Hax.Folds.fold_enumerated_slice (row
                <:
                t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
              (fun result temp_1_ ->
                  let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                    v_ROWS_IN_A =
                    result
                  in
                  let _:usize = temp_1_ in
                  true)
              result
              (fun result temp_1_ ->
                  let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                    v_ROWS_IN_A =
                    result
                  in
                  let j, ring_element:(usize &
                    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
                    temp_1_
                  in
                  let product:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
                    Libcrux_ml_dsa.Ntt.ntt_multiply_montgomery #v_SIMDUnit
                      ring_element
                      (Libcrux_ml_dsa.Ntt.ntt #v_SIMDUnit
                          (mask.[ j ]
                            <:
                            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                        <:
                        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                  in
                  let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                    v_ROWS_IN_A =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
                      i
                      (Libcrux_ml_dsa.Polynomial.impl__add #v_SIMDUnit
                          (result.[ i ]
                            <:
                            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                          product
                        <:
                        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                  in
                  result)
          in
          let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_ROWS_IN_A =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
              i
              (Libcrux_ml_dsa.Ntt.invert_ntt_montgomery #v_SIMDUnit
                  (result.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                <:
                Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          in
          result)
  in
  result

let compute_As1_plus_s2
      (#v_SIMDUnit: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (v_A_as_ntt:
          t_Array
            (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
            v_ROWS_IN_A)
      (s1: t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      (s2: t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A)
     =
  let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__ZERO #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      v_ROWS_IN_A
  in
  let s1_ntt:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A =
    Core.Array.impl_23__map #(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      v_COLUMNS_IN_A
      #(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      s1
      (fun s ->
          let s:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit = s in
          Libcrux_ml_dsa.Ntt.ntt #v_SIMDUnit s
          <:
          Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
  in
  let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A =
    Rust_primitives.Hax.Folds.fold_enumerated_slice (v_A_as_ntt
        <:
        t_Slice
        (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A))
      (fun result temp_1_ ->
          let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_ROWS_IN_A =
            result
          in
          let _:usize = temp_1_ in
          true)
      result
      (fun result temp_1_ ->
          let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_ROWS_IN_A =
            result
          in
          let i, row:(usize &
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A) =
            temp_1_
          in
          let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_ROWS_IN_A =
            Rust_primitives.Hax.Folds.fold_enumerated_slice (row
                <:
                t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
              (fun result temp_1_ ->
                  let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                    v_ROWS_IN_A =
                    result
                  in
                  let _:usize = temp_1_ in
                  true)
              result
              (fun result temp_1_ ->
                  let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                    v_ROWS_IN_A =
                    result
                  in
                  let j, ring_element:(usize &
                    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
                    temp_1_
                  in
                  let product:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
                    Libcrux_ml_dsa.Ntt.ntt_multiply_montgomery #v_SIMDUnit
                      ring_element
                      (s1_ntt.[ j ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                  in
                  let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                    v_ROWS_IN_A =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
                      i
                      (Libcrux_ml_dsa.Polynomial.impl__add #v_SIMDUnit
                          (result.[ i ]
                            <:
                            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                          product
                        <:
                        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                  in
                  result)
          in
          let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_ROWS_IN_A =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
              i
              (Libcrux_ml_dsa.Ntt.invert_ntt_montgomery #v_SIMDUnit
                  (result.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                <:
                Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          in
          let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_ROWS_IN_A =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
              i
              (Libcrux_ml_dsa.Polynomial.impl__add #v_SIMDUnit
                  (result.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                  (s2.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                <:
                Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          in
          result)
  in
  result

let compute_w_approx
      (#v_SIMDUnit: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (v_A_as_ntt:
          t_Array
            (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
            v_ROWS_IN_A)
      (signer_response:
          t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      (verifier_challenge_as_ntt: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      (t1: t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A)
     =
  let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__ZERO #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      v_ROWS_IN_A
  in
  let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A =
    Rust_primitives.Hax.Folds.fold_enumerated_slice (v_A_as_ntt
        <:
        t_Slice
        (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A))
      (fun result temp_1_ ->
          let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_ROWS_IN_A =
            result
          in
          let _:usize = temp_1_ in
          true)
      result
      (fun result temp_1_ ->
          let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_ROWS_IN_A =
            result
          in
          let i, row:(usize &
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A) =
            temp_1_
          in
          let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_ROWS_IN_A =
            Rust_primitives.Hax.Folds.fold_enumerated_slice (row
                <:
                t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
              (fun result temp_1_ ->
                  let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                    v_ROWS_IN_A =
                    result
                  in
                  let _:usize = temp_1_ in
                  true)
              result
              (fun result temp_1_ ->
                  let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                    v_ROWS_IN_A =
                    result
                  in
                  let j, ring_element:(usize &
                    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
                    temp_1_
                  in
                  let product:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
                    Libcrux_ml_dsa.Ntt.ntt_multiply_montgomery #v_SIMDUnit
                      ring_element
                      (Libcrux_ml_dsa.Ntt.ntt #v_SIMDUnit
                          (signer_response.[ j ]
                            <:
                            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                        <:
                        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                  in
                  let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                    v_ROWS_IN_A =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
                      i
                      (Libcrux_ml_dsa.Polynomial.impl__add #v_SIMDUnit
                          (result.[ i ]
                            <:
                            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                          product
                        <:
                        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                  in
                  result)
          in
          let t1_shifted:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
            Libcrux_ml_dsa.Arithmetic.shift_left_then_reduce #v_SIMDUnit
              13l
              (t1.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          in
          let challenge_times_t1_shifted:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement
          v_SIMDUnit =
            Libcrux_ml_dsa.Ntt.ntt_multiply_montgomery #v_SIMDUnit
              verifier_challenge_as_ntt
              (Libcrux_ml_dsa.Ntt.ntt #v_SIMDUnit t1_shifted
                <:
                Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          in
          let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_ROWS_IN_A =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
              i
              (Libcrux_ml_dsa.Ntt.invert_ntt_montgomery #v_SIMDUnit
                  (Libcrux_ml_dsa.Polynomial.impl__subtract #v_SIMDUnit
                      (result.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                      challenge_times_t1_shifted
                    <:
                    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                <:
                Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          in
          result)
  in
  result

let subtract_vectors
      (#v_SIMDUnit: Type0)
      (v_DIMENSION: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (lhs rhs: t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION)
     =
  let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__ZERO #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      v_DIMENSION
  in
  let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      v_DIMENSION
      (fun result temp_1_ ->
          let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_DIMENSION =
            result
          in
          let _:usize = temp_1_ in
          true)
      result
      (fun result i ->
          let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_DIMENSION =
            result
          in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
            i
            (Libcrux_ml_dsa.Polynomial.impl__subtract #v_SIMDUnit
                (lhs.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                (rhs.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
              <:
              Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          <:
          t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION)
  in
  result
