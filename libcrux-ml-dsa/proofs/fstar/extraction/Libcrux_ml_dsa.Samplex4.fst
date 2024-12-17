module Libcrux_ml_dsa.Samplex4
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Hash_functions.Shake256 in
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

let generate_domain_separator (row column: u8) =
  (cast (column <: u8) <: u16) |. ((cast (row <: u8) <: u16) <<! 8l <: u16)

let update_matrix
      (#v_SIMDUnit: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (m:
          t_Array
            (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
            v_ROWS_IN_A)
      (i j: usize)
      (v: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
     =
  let m:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize m
      i
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (m.[ i ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          j
          v
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  m

let matrix_A_4_by_4_
      (#v_SIMDUnit: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (seed: t_Array u8 (sz 34))
     =
  let
  (v_A:
    t_Array (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      v_ROWS_IN_A):t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__ZERO #v_SIMDUnit
              ()
            <:
            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          v_COLUMNS_IN_A
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      v_ROWS_IN_A
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      seed
      (generate_domain_separator 0uy 0uy <: u16)
      (generate_domain_separator 0uy 1uy <: u16)
      (generate_domain_separator 0uy 2uy <: u16)
      (generate_domain_separator 0uy 3uy <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 0) (sz 0) four_ring_elements._1
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 0) (sz 1) four_ring_elements._2
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 0) (sz 2) four_ring_elements._3
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 0) (sz 3) four_ring_elements._4
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      seed
      (generate_domain_separator 1uy 0uy <: u16)
      (generate_domain_separator 1uy 1uy <: u16)
      (generate_domain_separator 1uy 2uy <: u16)
      (generate_domain_separator 1uy 3uy <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 1) (sz 0) four_ring_elements._1
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 1) (sz 1) four_ring_elements._2
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 1) (sz 2) four_ring_elements._3
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 1) (sz 3) four_ring_elements._4
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      seed
      (generate_domain_separator 2uy 0uy <: u16)
      (generate_domain_separator 2uy 1uy <: u16)
      (generate_domain_separator 2uy 2uy <: u16)
      (generate_domain_separator 2uy 3uy <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 2) (sz 0) four_ring_elements._1
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 2) (sz 1) four_ring_elements._2
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 2) (sz 2) four_ring_elements._3
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 2) (sz 3) four_ring_elements._4
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      seed
      (generate_domain_separator 3uy 0uy <: u16)
      (generate_domain_separator 3uy 1uy <: u16)
      (generate_domain_separator 3uy 2uy <: u16)
      (generate_domain_separator 3uy 3uy <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 3) (sz 0) four_ring_elements._1
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 3) (sz 1) four_ring_elements._2
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 3) (sz 2) four_ring_elements._3
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 3) (sz 3) four_ring_elements._4
  in
  v_A

let matrix_A_6_by_5_
      (#v_SIMDUnit: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (seed: t_Array u8 (sz 34))
     =
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__ZERO #v_SIMDUnit
              ()
            <:
            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          v_COLUMNS_IN_A
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      v_ROWS_IN_A
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      seed
      (generate_domain_separator 0uy 0uy <: u16)
      (generate_domain_separator 0uy 1uy <: u16)
      (generate_domain_separator 0uy 2uy <: u16)
      (generate_domain_separator 0uy 3uy <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 0) (sz 0) four_ring_elements._1
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 0) (sz 1) four_ring_elements._2
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 0) (sz 2) four_ring_elements._3
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 0) (sz 3) four_ring_elements._4
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      seed
      (generate_domain_separator 0uy 4uy <: u16)
      (generate_domain_separator 1uy 0uy <: u16)
      (generate_domain_separator 1uy 1uy <: u16)
      (generate_domain_separator 1uy 2uy <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 0) (sz 4) four_ring_elements._1
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 1) (sz 0) four_ring_elements._2
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 1) (sz 1) four_ring_elements._3
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 1) (sz 2) four_ring_elements._4
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      seed
      (generate_domain_separator 1uy 3uy <: u16)
      (generate_domain_separator 1uy 4uy <: u16)
      (generate_domain_separator 2uy 0uy <: u16)
      (generate_domain_separator 2uy 1uy <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 1) (sz 3) four_ring_elements._1
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 1) (sz 4) four_ring_elements._2
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 2) (sz 0) four_ring_elements._3
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 2) (sz 1) four_ring_elements._4
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      seed
      (generate_domain_separator 2uy 2uy <: u16)
      (generate_domain_separator 2uy 3uy <: u16)
      (generate_domain_separator 2uy 4uy <: u16)
      (generate_domain_separator 3uy 0uy <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 2) (sz 2) four_ring_elements._1
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 2) (sz 3) four_ring_elements._2
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 2) (sz 4) four_ring_elements._3
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 3) (sz 0) four_ring_elements._4
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      seed
      (generate_domain_separator 3uy 1uy <: u16)
      (generate_domain_separator 3uy 2uy <: u16)
      (generate_domain_separator 3uy 3uy <: u16)
      (generate_domain_separator 3uy 4uy <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 3) (sz 1) four_ring_elements._1
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 3) (sz 2) four_ring_elements._2
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 3) (sz 3) four_ring_elements._3
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 3) (sz 4) four_ring_elements._4
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      seed
      (generate_domain_separator 4uy 0uy <: u16)
      (generate_domain_separator 4uy 1uy <: u16)
      (generate_domain_separator 4uy 2uy <: u16)
      (generate_domain_separator 4uy 3uy <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 4) (sz 0) four_ring_elements._1
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 4) (sz 1) four_ring_elements._2
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 4) (sz 2) four_ring_elements._3
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 4) (sz 3) four_ring_elements._4
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      seed
      (generate_domain_separator 4uy 4uy <: u16)
      (generate_domain_separator 5uy 0uy <: u16)
      (generate_domain_separator 5uy 1uy <: u16)
      (generate_domain_separator 5uy 2uy <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 4) (sz 4) four_ring_elements._1
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 5) (sz 0) four_ring_elements._2
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 5) (sz 1) four_ring_elements._3
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 5) (sz 2) four_ring_elements._4
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      seed
      (generate_domain_separator 5uy 3uy <: u16)
      (generate_domain_separator 5uy 4uy <: u16)
      (generate_domain_separator 5uy 5uy <: u16)
      (generate_domain_separator 5uy 6uy <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 5) (sz 3) four_ring_elements._1
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 5) (sz 4) four_ring_elements._2
  in
  v_A

let matrix_A_8_by_7_
      (#v_SIMDUnit: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (seed: t_Array u8 (sz 34))
     =
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__ZERO #v_SIMDUnit
              ()
            <:
            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          v_COLUMNS_IN_A
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      v_ROWS_IN_A
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      seed
      (generate_domain_separator 0uy 0uy <: u16)
      (generate_domain_separator 0uy 1uy <: u16)
      (generate_domain_separator 0uy 2uy <: u16)
      (generate_domain_separator 0uy 3uy <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 0) (sz 0) four_ring_elements._1
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 0) (sz 1) four_ring_elements._2
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 0) (sz 2) four_ring_elements._3
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 0) (sz 3) four_ring_elements._4
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      seed
      (generate_domain_separator 0uy 4uy <: u16)
      (generate_domain_separator 0uy 5uy <: u16)
      (generate_domain_separator 0uy 6uy <: u16)
      (generate_domain_separator 1uy 0uy <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 0) (sz 4) four_ring_elements._1
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 0) (sz 5) four_ring_elements._2
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 0) (sz 6) four_ring_elements._3
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 1) (sz 0) four_ring_elements._4
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      seed
      (generate_domain_separator 1uy 1uy <: u16)
      (generate_domain_separator 1uy 2uy <: u16)
      (generate_domain_separator 1uy 3uy <: u16)
      (generate_domain_separator 1uy 4uy <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 1) (sz 1) four_ring_elements._1
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 1) (sz 2) four_ring_elements._2
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 1) (sz 3) four_ring_elements._3
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 1) (sz 4) four_ring_elements._4
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      seed
      (generate_domain_separator 1uy 5uy <: u16)
      (generate_domain_separator 1uy 6uy <: u16)
      (generate_domain_separator 2uy 0uy <: u16)
      (generate_domain_separator 2uy 1uy <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 1) (sz 5) four_ring_elements._1
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 1) (sz 6) four_ring_elements._2
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 2) (sz 0) four_ring_elements._3
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 2) (sz 1) four_ring_elements._4
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      seed
      (generate_domain_separator 2uy 2uy <: u16)
      (generate_domain_separator 2uy 3uy <: u16)
      (generate_domain_separator 2uy 4uy <: u16)
      (generate_domain_separator 2uy 5uy <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 2) (sz 2) four_ring_elements._1
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 2) (sz 3) four_ring_elements._2
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 2) (sz 4) four_ring_elements._3
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 2) (sz 5) four_ring_elements._4
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      seed
      (generate_domain_separator 2uy 6uy <: u16)
      (generate_domain_separator 3uy 0uy <: u16)
      (generate_domain_separator 3uy 1uy <: u16)
      (generate_domain_separator 3uy 2uy <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 2) (sz 6) four_ring_elements._1
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 3) (sz 0) four_ring_elements._2
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 3) (sz 1) four_ring_elements._3
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 3) (sz 2) four_ring_elements._4
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      seed
      (generate_domain_separator 3uy 3uy <: u16)
      (generate_domain_separator 3uy 4uy <: u16)
      (generate_domain_separator 3uy 5uy <: u16)
      (generate_domain_separator 3uy 6uy <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 3) (sz 3) four_ring_elements._1
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 3) (sz 4) four_ring_elements._2
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 3) (sz 5) four_ring_elements._3
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 3) (sz 6) four_ring_elements._4
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      seed
      (generate_domain_separator 4uy 0uy <: u16)
      (generate_domain_separator 4uy 1uy <: u16)
      (generate_domain_separator 4uy 2uy <: u16)
      (generate_domain_separator 4uy 3uy <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 4) (sz 0) four_ring_elements._1
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 4) (sz 1) four_ring_elements._2
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 4) (sz 2) four_ring_elements._3
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 4) (sz 3) four_ring_elements._4
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      seed
      (generate_domain_separator 4uy 4uy <: u16)
      (generate_domain_separator 4uy 5uy <: u16)
      (generate_domain_separator 4uy 6uy <: u16)
      (generate_domain_separator 5uy 0uy <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 4) (sz 4) four_ring_elements._1
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 4) (sz 5) four_ring_elements._2
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 4) (sz 6) four_ring_elements._3
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 5) (sz 0) four_ring_elements._4
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      seed
      (generate_domain_separator 5uy 1uy <: u16)
      (generate_domain_separator 5uy 2uy <: u16)
      (generate_domain_separator 5uy 3uy <: u16)
      (generate_domain_separator 5uy 4uy <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 5) (sz 1) four_ring_elements._1
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 5) (sz 2) four_ring_elements._2
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 5) (sz 3) four_ring_elements._3
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 5) (sz 4) four_ring_elements._4
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      seed
      (generate_domain_separator 5uy 5uy <: u16)
      (generate_domain_separator 5uy 6uy <: u16)
      (generate_domain_separator 6uy 0uy <: u16)
      (generate_domain_separator 6uy 1uy <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 5) (sz 5) four_ring_elements._1
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 5) (sz 6) four_ring_elements._2
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 6) (sz 0) four_ring_elements._3
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 6) (sz 1) four_ring_elements._4
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      seed
      (generate_domain_separator 6uy 2uy <: u16)
      (generate_domain_separator 6uy 3uy <: u16)
      (generate_domain_separator 6uy 4uy <: u16)
      (generate_domain_separator 6uy 5uy <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 6) (sz 2) four_ring_elements._1
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 6) (sz 3) four_ring_elements._2
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 6) (sz 4) four_ring_elements._3
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 6) (sz 5) four_ring_elements._4
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      seed
      (generate_domain_separator 6uy 6uy <: u16)
      (generate_domain_separator 7uy 0uy <: u16)
      (generate_domain_separator 7uy 1uy <: u16)
      (generate_domain_separator 7uy 2uy <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 6) (sz 6) four_ring_elements._1
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 7) (sz 0) four_ring_elements._2
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 7) (sz 1) four_ring_elements._3
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 7) (sz 2) four_ring_elements._4
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      seed
      (generate_domain_separator 7uy 3uy <: u16)
      (generate_domain_separator 7uy 4uy <: u16)
      (generate_domain_separator 7uy 5uy <: u16)
      (generate_domain_separator 7uy 6uy <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 7) (sz 3) four_ring_elements._1
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 7) (sz 4) four_ring_elements._2
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 7) (sz 5) four_ring_elements._3
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    update_matrix #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A v_A (sz 7) (sz 6) four_ring_elements._4
  in
  v_A

let matrix_A
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
  | 4uy, 4uy -> matrix_A_4_by_4_ #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A seed
  | 6uy, 5uy -> matrix_A_6_by_5_ #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A seed
  | 8uy, 7uy -> matrix_A_8_by_7_ #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A seed
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

let sample_s1_and_s2_4_by_4_
      (#v_SIMDUnit #v_Shake256X4: Type0)
      (v_ETA v_S1_DIMENSION v_S2_DIMENSION: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4)
      (seed_base: t_Array u8 (sz 66))
     =
  let s1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__ZERO #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      v_S1_DIMENSION
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__ZERO #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      v_S2_DIMENSION
  in
  let four:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_error_ring_elements #v_SIMDUnit
      #v_Shake256X4
      v_ETA
      seed_base
      0us
      1us
      2us
      3us
  in
  let s1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s1 (sz 0) four._1
  in
  let s1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s1 (sz 1) four._2
  in
  let s1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s1 (sz 2) four._3
  in
  let s1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s1 (sz 3) four._4
  in
  let four:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_error_ring_elements #v_SIMDUnit
      #v_Shake256X4
      v_ETA
      seed_base
      4us
      5us
      6us
      7us
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2 (sz 0) four._1
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2 (sz 1) four._2
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2 (sz 2) four._3
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2 (sz 3) four._4
  in
  s1, s2
  <:
  (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION &
    t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION)

let sample_s1_and_s2_5_by_6_
      (#v_SIMDUnit #v_Shake256X4: Type0)
      (v_ETA v_S1_DIMENSION v_S2_DIMENSION: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4)
      (seed_base: t_Array u8 (sz 66))
     =
  let s1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__ZERO #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      v_S1_DIMENSION
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__ZERO #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      v_S2_DIMENSION
  in
  let four:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_error_ring_elements #v_SIMDUnit
      #v_Shake256X4
      v_ETA
      seed_base
      0us
      1us
      2us
      3us
  in
  let s1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s1 (sz 0) four._1
  in
  let s1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s1 (sz 1) four._2
  in
  let s1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s1 (sz 2) four._3
  in
  let s1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s1 (sz 3) four._4
  in
  let four:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_error_ring_elements #v_SIMDUnit
      #v_Shake256X4
      v_ETA
      seed_base
      4us
      5us
      6us
      7us
  in
  let s1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s1 (sz 4) four._1
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2 (sz 0) four._2
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2 (sz 1) four._3
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2 (sz 2) four._4
  in
  let four:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_error_ring_elements #v_SIMDUnit
      #v_Shake256X4
      v_ETA
      seed_base
      8us
      9us
      10us
      11us
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2 (sz 3) four._1
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2 (sz 4) four._2
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2 (sz 5) four._3
  in
  s1, s2
  <:
  (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION &
    t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION)

let sample_s1_and_s2_7_by_8_
      (#v_SIMDUnit #v_Shake256X4: Type0)
      (v_ETA v_S1_DIMENSION v_S2_DIMENSION: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4)
      (seed_base: t_Array u8 (sz 66))
     =
  let s1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__ZERO #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      v_S1_DIMENSION
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__ZERO #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      v_S2_DIMENSION
  in
  let four:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_error_ring_elements #v_SIMDUnit
      #v_Shake256X4
      v_ETA
      seed_base
      0us
      1us
      2us
      3us
  in
  let s1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s1 (sz 0) four._1
  in
  let s1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s1 (sz 1) four._2
  in
  let s1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s1 (sz 2) four._3
  in
  let s1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s1 (sz 3) four._4
  in
  let four:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_error_ring_elements #v_SIMDUnit
      #v_Shake256X4
      v_ETA
      seed_base
      4us
      5us
      6us
      7us
  in
  let s1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s1 (sz 4) four._1
  in
  let s1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s1 (sz 5) four._2
  in
  let s1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s1 (sz 6) four._3
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2 (sz 0) four._4
  in
  let four:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_error_ring_elements #v_SIMDUnit
      #v_Shake256X4
      v_ETA
      seed_base
      8us
      9us
      10us
      11us
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2 (sz 1) four._1
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2 (sz 2) four._2
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2 (sz 3) four._3
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2 (sz 4) four._4
  in
  let four:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_error_ring_elements #v_SIMDUnit
      #v_Shake256X4
      v_ETA
      seed_base
      12us
      13us
      14us
      15us
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2 (sz 5) four._1
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2 (sz 6) four._2
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2 (sz 7) four._3
  in
  s1, s2
  <:
  (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION &
    t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION)

let sample_s1_and_s2
      (#v_SIMDUnit #v_Shake256X4: Type0)
      (v_ETA v_S1_DIMENSION v_S2_DIMENSION: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4)
      (seed: t_Array u8 (sz 66))
     =
  match
    (cast (v_S1_DIMENSION <: usize) <: u8), (cast (v_S2_DIMENSION <: usize) <: u8) <: (u8 & u8)
  with
  | 4uy, 4uy ->
    sample_s1_and_s2_4_by_4_ #v_SIMDUnit #v_Shake256X4 v_ETA v_S1_DIMENSION v_S2_DIMENSION seed
  | 5uy, 6uy ->
    sample_s1_and_s2_5_by_6_ #v_SIMDUnit #v_Shake256X4 v_ETA v_S1_DIMENSION v_S2_DIMENSION seed
  | 7uy, 8uy ->
    sample_s1_and_s2_7_by_8_ #v_SIMDUnit #v_Shake256X4 v_ETA v_S1_DIMENSION v_S2_DIMENSION seed
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)
