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
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (vector: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (ring_element: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
     =
  let vector:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (Core.Slice.impl__len #(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) vector
        <:
        usize)
      (fun vector temp_1_ ->
          let vector:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
            vector
          in
          let _:usize = temp_1_ in
          true)
      vector
      (fun vector i ->
          let vector:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
            vector
          in
          let i:usize = i in
          let vector:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize vector
              i
              (Libcrux_ml_dsa.Ntt.ntt_multiply_montgomery #v_SIMDUnit
                  (vector.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                  ring_element
                <:
                Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          in
          let vector:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize vector
              i
              (Libcrux_ml_dsa.Ntt.invert_ntt_montgomery #v_SIMDUnit
                  (vector.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                <:
                Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          in
          vector)
  in
  vector

let add_vectors
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (dimension: usize)
      (lhs rhs: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
     =
  let lhs:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      dimension
      (fun lhs temp_1_ ->
          let lhs:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) = lhs in
          let _:usize = temp_1_ in
          true)
      lhs
      (fun lhs i ->
          let lhs:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) = lhs in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize lhs
            i
            (Libcrux_ml_dsa.Polynomial.impl__add #v_SIMDUnit
                (lhs.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                (rhs.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
              <:
              Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          <:
          t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
  in
  lhs

let compute_as1_plus_s2
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (rows_in_a columns_in_a: usize)
      (a_as_ntt s1_ntt s1_s2 result:
          t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
     =
  let result:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      rows_in_a
      (fun result temp_1_ ->
          let result:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
            result
          in
          let _:usize = temp_1_ in
          true)
      result
      (fun result i ->
          let result:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
            result
          in
          let i:usize = i in
          Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
            columns_in_a
            (fun result temp_1_ ->
                let result:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
                  result
                in
                let _:usize = temp_1_ in
                true)
            result
            (fun result j ->
                let result:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
                  result
                in
                let j:usize = j in
                let product:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
                  a_as_ntt.[ (i *! columns_in_a <: usize) +! j <: usize ]
                in
                let product:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
                  Libcrux_ml_dsa.Ntt.ntt_multiply_montgomery #v_SIMDUnit
                    product
                    (s1_ntt.[ j ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                in
                let result:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
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
          <:
          t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
  in
  let result:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (Core.Slice.impl__len #(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) result
        <:
        usize)
      (fun result temp_1_ ->
          let result:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
            result
          in
          let _:usize = temp_1_ in
          true)
      result
      (fun result i ->
          let result:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
            result
          in
          let i:usize = i in
          let result:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
              i
              (Libcrux_ml_dsa.Ntt.invert_ntt_montgomery #v_SIMDUnit
                  (result.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                <:
                Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          in
          let result:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
              i
              (Libcrux_ml_dsa.Polynomial.impl__add #v_SIMDUnit
                  (result.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                  (s1_s2.[ columns_in_a +! i <: usize ]
                    <:
                    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                <:
                Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          in
          result)
  in
  result

let compute_matrix_x_mask
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (rows_in_a columns_in_a: usize)
      (matrix mask result: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
     =
  let result:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      rows_in_a
      (fun result temp_1_ ->
          let result:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
            result
          in
          let _:usize = temp_1_ in
          true)
      result
      (fun result i ->
          let result:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
            result
          in
          let i:usize = i in
          let result:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
            Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
              columns_in_a
              (fun result temp_1_ ->
                  let result:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                  =
                    result
                  in
                  let _:usize = temp_1_ in
                  true)
              result
              (fun result j ->
                  let result:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                  =
                    result
                  in
                  let j:usize = j in
                  let product:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
                    mask.[ j ]
                  in
                  let product:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
                    Libcrux_ml_dsa.Ntt.ntt_multiply_montgomery #v_SIMDUnit
                      product
                      (matrix.[ (i *! columns_in_a <: usize) +! j <: usize ]
                        <:
                        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                  in
                  let result:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                  =
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
          let result:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
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

let compute_w_approx
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (rows_in_a columns_in_a: usize)
      (matrix signer_response:
          t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (verifier_challenge_as_ntt: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      (t1: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
     =
  let t1:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      rows_in_a
      (fun t1 temp_1_ ->
          let t1:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) = t1 in
          let _:usize = temp_1_ in
          true)
      t1
      (fun t1 i ->
          let t1:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) = t1 in
          let i:usize = i in
          let inner_result:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
            Libcrux_ml_dsa.Polynomial.impl__zero #v_SIMDUnit ()
          in
          let inner_result:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
            Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
              columns_in_a
              (fun inner_result temp_1_ ->
                  let inner_result:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
                    inner_result
                  in
                  let _:usize = temp_1_ in
                  true)
              inner_result
              (fun inner_result j ->
                  let inner_result:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
                    inner_result
                  in
                  let j:usize = j in
                  let product:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
                    matrix.[ (i *! columns_in_a <: usize) +! j <: usize ]
                  in
                  let product:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
                    Libcrux_ml_dsa.Ntt.ntt_multiply_montgomery #v_SIMDUnit
                      product
                      (signer_response.[ j ]
                        <:
                        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                  in
                  let inner_result:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
                    Libcrux_ml_dsa.Polynomial.impl__add #v_SIMDUnit inner_result product
                  in
                  inner_result)
          in
          let t1:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize t1
              i
              (Libcrux_ml_dsa.Arithmetic.shift_left_then_reduce #v_SIMDUnit
                  (mk_i32 13)
                  (t1.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                <:
                Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          in
          let t1:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize t1
              i
              (Libcrux_ml_dsa.Ntt.ntt #v_SIMDUnit
                  (t1.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                <:
                Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          in
          let t1:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize t1
              i
              (Libcrux_ml_dsa.Ntt.ntt_multiply_montgomery #v_SIMDUnit
                  (t1.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                  verifier_challenge_as_ntt
                <:
                Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          in
          let inner_result:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
            Libcrux_ml_dsa.Polynomial.impl__subtract #v_SIMDUnit
              inner_result
              (t1.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          in
          let t1:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize t1 i inner_result
          in
          let t1:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize t1
              i
              (Libcrux_ml_dsa.Ntt.invert_ntt_montgomery #v_SIMDUnit
                  (t1.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                <:
                Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          in
          t1)
  in
  t1

let subtract_vectors
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (dimension: usize)
      (lhs rhs: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
     =
  let lhs:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      dimension
      (fun lhs temp_1_ ->
          let lhs:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) = lhs in
          let _:usize = temp_1_ in
          true)
      lhs
      (fun lhs i ->
          let lhs:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) = lhs in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize lhs
            i
            (Libcrux_ml_dsa.Polynomial.impl__subtract #v_SIMDUnit
                (lhs.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                (rhs.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
              <:
              Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          <:
          t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
  in
  lhs
