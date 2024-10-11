module Libcrux_ml_dsa.Samplex4
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Hash_functions.Shake128 in
  let open Libcrux_ml_dsa.Hash_functions.Shake256 in
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

let generate_domain_separator (row column: u8) : u16 =
  (cast (column <: u8) <: u16) |. ((cast (row <: u8) <: u16) <<! Rust_primitives.mk_i32 8 <: u16)

let matrix_A_4_by_4_
      (#v_SIMDUnit #v_Shake128X4: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4)
      (seed: t_Array u8 (Rust_primitives.mk_usize 34))
    : t_Array
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      v_ROWS_IN_A =
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
      #v_Shake128X4
      seed
      (generate_domain_separator (Rust_primitives.mk_u8 0) (Rust_primitives.mk_u8 0) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 0) (Rust_primitives.mk_u8 1) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 0) (Rust_primitives.mk_u8 2) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 0) (Rust_primitives.mk_u8 3) <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 0)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 0
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 0)
          four_ring_elements._1
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 0)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 0
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 1)
          four_ring_elements._2
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 0)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 0
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 2)
          four_ring_elements._3
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 0)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 0
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 3)
          four_ring_elements._4
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      #v_Shake128X4
      seed
      (generate_domain_separator (Rust_primitives.mk_u8 1) (Rust_primitives.mk_u8 0) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 1) (Rust_primitives.mk_u8 1) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 1) (Rust_primitives.mk_u8 2) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 1) (Rust_primitives.mk_u8 3) <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 1)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 1
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 0)
          four_ring_elements._1
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 1)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 1
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 1)
          four_ring_elements._2
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 1)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 1
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 2)
          four_ring_elements._3
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 1)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 1
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 3)
          four_ring_elements._4
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      #v_Shake128X4
      seed
      (generate_domain_separator (Rust_primitives.mk_u8 2) (Rust_primitives.mk_u8 0) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 2) (Rust_primitives.mk_u8 1) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 2) (Rust_primitives.mk_u8 2) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 2) (Rust_primitives.mk_u8 3) <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 2)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 2
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 0)
          four_ring_elements._1
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 2)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 2
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 1)
          four_ring_elements._2
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 2)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 2
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 2)
          four_ring_elements._3
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 2)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 2
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 3)
          four_ring_elements._4
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      #v_Shake128X4
      seed
      (generate_domain_separator (Rust_primitives.mk_u8 3) (Rust_primitives.mk_u8 0) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 3) (Rust_primitives.mk_u8 1) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 3) (Rust_primitives.mk_u8 2) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 3) (Rust_primitives.mk_u8 3) <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 3)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 3
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 0)
          four_ring_elements._1
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 3)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 3
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 1)
          four_ring_elements._2
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 3)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 3
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 2)
          four_ring_elements._3
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 3)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 3
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 3)
          four_ring_elements._4
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  v_A

let matrix_A_6_by_5_
      (#v_SIMDUnit #v_Shake128X4: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4)
      (seed: t_Array u8 (Rust_primitives.mk_usize 34))
    : t_Array
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      v_ROWS_IN_A =
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
      #v_Shake128X4
      seed
      (generate_domain_separator (Rust_primitives.mk_u8 0) (Rust_primitives.mk_u8 0) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 0) (Rust_primitives.mk_u8 1) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 0) (Rust_primitives.mk_u8 2) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 0) (Rust_primitives.mk_u8 3) <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 0)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 0
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 0)
          four_ring_elements._1
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 0)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 0
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 1)
          four_ring_elements._2
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 0)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 0
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 2)
          four_ring_elements._3
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 0)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 0
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 3)
          four_ring_elements._4
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      #v_Shake128X4
      seed
      (generate_domain_separator (Rust_primitives.mk_u8 0) (Rust_primitives.mk_u8 4) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 1) (Rust_primitives.mk_u8 0) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 1) (Rust_primitives.mk_u8 1) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 1) (Rust_primitives.mk_u8 2) <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 0)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 0
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 4)
          four_ring_elements._1
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 1)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 1
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 0)
          four_ring_elements._2
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 1)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 1
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 1)
          four_ring_elements._3
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 1)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 1
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 2)
          four_ring_elements._4
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      #v_Shake128X4
      seed
      (generate_domain_separator (Rust_primitives.mk_u8 1) (Rust_primitives.mk_u8 3) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 1) (Rust_primitives.mk_u8 4) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 2) (Rust_primitives.mk_u8 0) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 2) (Rust_primitives.mk_u8 1) <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 1)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 1
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 3)
          four_ring_elements._1
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 1)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 1
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 4)
          four_ring_elements._2
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 2)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 2
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 0)
          four_ring_elements._3
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 2)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 2
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 1)
          four_ring_elements._4
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      #v_Shake128X4
      seed
      (generate_domain_separator (Rust_primitives.mk_u8 2) (Rust_primitives.mk_u8 2) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 2) (Rust_primitives.mk_u8 3) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 2) (Rust_primitives.mk_u8 4) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 3) (Rust_primitives.mk_u8 0) <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 2)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 2
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 2)
          four_ring_elements._1
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 2)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 2
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 3)
          four_ring_elements._2
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 2)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 2
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 4)
          four_ring_elements._3
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 3)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 3
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 0)
          four_ring_elements._4
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      #v_Shake128X4
      seed
      (generate_domain_separator (Rust_primitives.mk_u8 3) (Rust_primitives.mk_u8 1) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 3) (Rust_primitives.mk_u8 2) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 3) (Rust_primitives.mk_u8 3) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 3) (Rust_primitives.mk_u8 4) <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 3)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 3
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 1)
          four_ring_elements._1
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 3)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 3
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 2)
          four_ring_elements._2
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 3)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 3
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 3)
          four_ring_elements._3
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 3)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 3
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 4)
          four_ring_elements._4
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      #v_Shake128X4
      seed
      (generate_domain_separator (Rust_primitives.mk_u8 4) (Rust_primitives.mk_u8 0) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 4) (Rust_primitives.mk_u8 1) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 4) (Rust_primitives.mk_u8 2) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 4) (Rust_primitives.mk_u8 3) <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 4)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 4
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 0)
          four_ring_elements._1
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 4)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 4
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 1)
          four_ring_elements._2
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 4)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 4
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 2)
          four_ring_elements._3
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 4)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 4
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 3)
          four_ring_elements._4
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      #v_Shake128X4
      seed
      (generate_domain_separator (Rust_primitives.mk_u8 4) (Rust_primitives.mk_u8 4) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 5) (Rust_primitives.mk_u8 0) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 5) (Rust_primitives.mk_u8 1) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 5) (Rust_primitives.mk_u8 2) <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 4)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 4
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 4)
          four_ring_elements._1
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 5)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 5
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 0)
          four_ring_elements._2
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 5)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 5
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 1)
          four_ring_elements._3
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 5)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 5
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 2)
          four_ring_elements._4
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      #v_Shake128X4
      seed
      (generate_domain_separator (Rust_primitives.mk_u8 5) (Rust_primitives.mk_u8 3) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 5) (Rust_primitives.mk_u8 4) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 5) (Rust_primitives.mk_u8 5) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 5) (Rust_primitives.mk_u8 6) <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 5)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 5
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 3)
          four_ring_elements._1
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 5)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 5
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 4)
          four_ring_elements._2
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  v_A

let matrix_A_8_by_7_
      (#v_SIMDUnit #v_Shake128X4: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4)
      (seed: t_Array u8 (Rust_primitives.mk_usize 34))
    : t_Array
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      v_ROWS_IN_A =
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
      #v_Shake128X4
      seed
      (generate_domain_separator (Rust_primitives.mk_u8 0) (Rust_primitives.mk_u8 0) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 0) (Rust_primitives.mk_u8 1) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 0) (Rust_primitives.mk_u8 2) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 0) (Rust_primitives.mk_u8 3) <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 0)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 0
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 0)
          four_ring_elements._1
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 0)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 0
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 1)
          four_ring_elements._2
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 0)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 0
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 2)
          four_ring_elements._3
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 0)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 0
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 3)
          four_ring_elements._4
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      #v_Shake128X4
      seed
      (generate_domain_separator (Rust_primitives.mk_u8 0) (Rust_primitives.mk_u8 4) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 0) (Rust_primitives.mk_u8 5) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 0) (Rust_primitives.mk_u8 6) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 1) (Rust_primitives.mk_u8 0) <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 0)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 0
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 4)
          four_ring_elements._1
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 0)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 0
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 5)
          four_ring_elements._2
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 0)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 0
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 6)
          four_ring_elements._3
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 1)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 1
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 0)
          four_ring_elements._4
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      #v_Shake128X4
      seed
      (generate_domain_separator (Rust_primitives.mk_u8 1) (Rust_primitives.mk_u8 1) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 1) (Rust_primitives.mk_u8 2) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 1) (Rust_primitives.mk_u8 3) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 1) (Rust_primitives.mk_u8 4) <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 1)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 1
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 1)
          four_ring_elements._1
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 1)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 1
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 2)
          four_ring_elements._2
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 1)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 1
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 3)
          four_ring_elements._3
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 1)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 1
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 4)
          four_ring_elements._4
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      #v_Shake128X4
      seed
      (generate_domain_separator (Rust_primitives.mk_u8 1) (Rust_primitives.mk_u8 5) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 1) (Rust_primitives.mk_u8 6) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 2) (Rust_primitives.mk_u8 0) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 2) (Rust_primitives.mk_u8 1) <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 1)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 1
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 5)
          four_ring_elements._1
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 1)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 1
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 6)
          four_ring_elements._2
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 2)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 2
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 0)
          four_ring_elements._3
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 2)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 2
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 1)
          four_ring_elements._4
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      #v_Shake128X4
      seed
      (generate_domain_separator (Rust_primitives.mk_u8 2) (Rust_primitives.mk_u8 2) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 2) (Rust_primitives.mk_u8 3) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 2) (Rust_primitives.mk_u8 4) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 2) (Rust_primitives.mk_u8 5) <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 2)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 2
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 2)
          four_ring_elements._1
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 2)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 2
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 3)
          four_ring_elements._2
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 2)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 2
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 4)
          four_ring_elements._3
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 2)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 2
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 5)
          four_ring_elements._4
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      #v_Shake128X4
      seed
      (generate_domain_separator (Rust_primitives.mk_u8 2) (Rust_primitives.mk_u8 6) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 3) (Rust_primitives.mk_u8 0) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 3) (Rust_primitives.mk_u8 1) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 3) (Rust_primitives.mk_u8 2) <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 2)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 2
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 6)
          four_ring_elements._1
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 3)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 3
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 0)
          four_ring_elements._2
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 3)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 3
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 1)
          four_ring_elements._3
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 3)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 3
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 2)
          four_ring_elements._4
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      #v_Shake128X4
      seed
      (generate_domain_separator (Rust_primitives.mk_u8 3) (Rust_primitives.mk_u8 3) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 3) (Rust_primitives.mk_u8 4) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 3) (Rust_primitives.mk_u8 5) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 3) (Rust_primitives.mk_u8 6) <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 3)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 3
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 3)
          four_ring_elements._1
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 3)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 3
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 4)
          four_ring_elements._2
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 3)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 3
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 5)
          four_ring_elements._3
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 3)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 3
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 6)
          four_ring_elements._4
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      #v_Shake128X4
      seed
      (generate_domain_separator (Rust_primitives.mk_u8 4) (Rust_primitives.mk_u8 0) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 4) (Rust_primitives.mk_u8 1) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 4) (Rust_primitives.mk_u8 2) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 4) (Rust_primitives.mk_u8 3) <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 4)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 4
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 0)
          four_ring_elements._1
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 4)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 4
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 1)
          four_ring_elements._2
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 4)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 4
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 2)
          four_ring_elements._3
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 4)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 4
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 3)
          four_ring_elements._4
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      #v_Shake128X4
      seed
      (generate_domain_separator (Rust_primitives.mk_u8 4) (Rust_primitives.mk_u8 4) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 4) (Rust_primitives.mk_u8 5) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 4) (Rust_primitives.mk_u8 6) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 5) (Rust_primitives.mk_u8 0) <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 4)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 4
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 4)
          four_ring_elements._1
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 4)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 4
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 5)
          four_ring_elements._2
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 4)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 4
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 6)
          four_ring_elements._3
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 5)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 5
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 0)
          four_ring_elements._4
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      #v_Shake128X4
      seed
      (generate_domain_separator (Rust_primitives.mk_u8 5) (Rust_primitives.mk_u8 1) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 5) (Rust_primitives.mk_u8 2) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 5) (Rust_primitives.mk_u8 3) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 5) (Rust_primitives.mk_u8 4) <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 5)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 5
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 1)
          four_ring_elements._1
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 5)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 5
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 2)
          four_ring_elements._2
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 5)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 5
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 3)
          four_ring_elements._3
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 5)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 5
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 4)
          four_ring_elements._4
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      #v_Shake128X4
      seed
      (generate_domain_separator (Rust_primitives.mk_u8 5) (Rust_primitives.mk_u8 5) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 5) (Rust_primitives.mk_u8 6) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 6) (Rust_primitives.mk_u8 0) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 6) (Rust_primitives.mk_u8 1) <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 5)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 5
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 5)
          four_ring_elements._1
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 5)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 5
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 6)
          four_ring_elements._2
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 6)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 6
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 0)
          four_ring_elements._3
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 6)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 6
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 1)
          four_ring_elements._4
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      #v_Shake128X4
      seed
      (generate_domain_separator (Rust_primitives.mk_u8 6) (Rust_primitives.mk_u8 2) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 6) (Rust_primitives.mk_u8 3) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 6) (Rust_primitives.mk_u8 4) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 6) (Rust_primitives.mk_u8 5) <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 6)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 6
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 2)
          four_ring_elements._1
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 6)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 6
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 3)
          four_ring_elements._2
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 6)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 6
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 4)
          four_ring_elements._3
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 6)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 6
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 5)
          four_ring_elements._4
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      #v_Shake128X4
      seed
      (generate_domain_separator (Rust_primitives.mk_u8 6) (Rust_primitives.mk_u8 6) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 7) (Rust_primitives.mk_u8 0) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 7) (Rust_primitives.mk_u8 1) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 7) (Rust_primitives.mk_u8 2) <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 6)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 6
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 6)
          four_ring_elements._1
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 7)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 7
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 0)
          four_ring_elements._2
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 7)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 7
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 1)
          four_ring_elements._3
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 7)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 7
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 2)
          four_ring_elements._4
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let four_ring_elements:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_ring_elements #v_SIMDUnit
      #v_Shake128X4
      seed
      (generate_domain_separator (Rust_primitives.mk_u8 7) (Rust_primitives.mk_u8 3) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 7) (Rust_primitives.mk_u8 4) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 7) (Rust_primitives.mk_u8 5) <: u16)
      (generate_domain_separator (Rust_primitives.mk_u8 7) (Rust_primitives.mk_u8 6) <: u16)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 7)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 7
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 3)
          four_ring_elements._1
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 7)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 7
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 4)
          four_ring_elements._2
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 7)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 7
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 5)
          four_ring_elements._3
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
      (Rust_primitives.mk_usize 7)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ Rust_primitives.mk_usize 7
            ]
            <:
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
          (Rust_primitives.mk_usize 6)
          four_ring_elements._4
        <:
        t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  v_A

let matrix_A
      (#v_SIMDUnit #v_Shake128X4: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4)
      (seed: t_Array u8 (Rust_primitives.mk_usize 34))
    : t_Array
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      v_ROWS_IN_A =
  match
    (cast (v_ROWS_IN_A <: usize) <: u8), (cast (v_COLUMNS_IN_A <: usize) <: u8) <: (u8 & u8)
  with
  | 4, 4 -> matrix_A_4_by_4_ #v_SIMDUnit #v_Shake128X4 v_ROWS_IN_A v_COLUMNS_IN_A seed
  | 6, 5 -> matrix_A_6_by_5_ #v_SIMDUnit #v_Shake128X4 v_ROWS_IN_A v_COLUMNS_IN_A seed
  | 8, 7 -> matrix_A_8_by_7_ #v_SIMDUnit #v_Shake128X4 v_ROWS_IN_A v_COLUMNS_IN_A seed
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
      (seed_base: t_Array u8 (Rust_primitives.mk_usize 66))
    : (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION &
      t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION) =
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
      (Rust_primitives.mk_u16 0)
      (Rust_primitives.mk_u16 1)
      (Rust_primitives.mk_u16 2)
      (Rust_primitives.mk_u16 3)
  in
  let s1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s1
      (Rust_primitives.mk_usize 0)
      four._1
  in
  let s1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s1
      (Rust_primitives.mk_usize 1)
      four._2
  in
  let s1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s1
      (Rust_primitives.mk_usize 2)
      four._3
  in
  let s1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s1
      (Rust_primitives.mk_usize 3)
      four._4
  in
  let four:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_error_ring_elements #v_SIMDUnit
      #v_Shake256X4
      v_ETA
      seed_base
      (Rust_primitives.mk_u16 4)
      (Rust_primitives.mk_u16 5)
      (Rust_primitives.mk_u16 6)
      (Rust_primitives.mk_u16 7)
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2
      (Rust_primitives.mk_usize 0)
      four._1
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2
      (Rust_primitives.mk_usize 1)
      four._2
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2
      (Rust_primitives.mk_usize 2)
      four._3
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2
      (Rust_primitives.mk_usize 3)
      four._4
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
      (seed_base: t_Array u8 (Rust_primitives.mk_usize 66))
    : (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION &
      t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION) =
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
      (Rust_primitives.mk_u16 0)
      (Rust_primitives.mk_u16 1)
      (Rust_primitives.mk_u16 2)
      (Rust_primitives.mk_u16 3)
  in
  let s1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s1
      (Rust_primitives.mk_usize 0)
      four._1
  in
  let s1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s1
      (Rust_primitives.mk_usize 1)
      four._2
  in
  let s1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s1
      (Rust_primitives.mk_usize 2)
      four._3
  in
  let s1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s1
      (Rust_primitives.mk_usize 3)
      four._4
  in
  let four:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_error_ring_elements #v_SIMDUnit
      #v_Shake256X4
      v_ETA
      seed_base
      (Rust_primitives.mk_u16 4)
      (Rust_primitives.mk_u16 5)
      (Rust_primitives.mk_u16 6)
      (Rust_primitives.mk_u16 7)
  in
  let s1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s1
      (Rust_primitives.mk_usize 4)
      four._1
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2
      (Rust_primitives.mk_usize 0)
      four._2
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2
      (Rust_primitives.mk_usize 1)
      four._3
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2
      (Rust_primitives.mk_usize 2)
      four._4
  in
  let four:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_error_ring_elements #v_SIMDUnit
      #v_Shake256X4
      v_ETA
      seed_base
      (Rust_primitives.mk_u16 8)
      (Rust_primitives.mk_u16 9)
      (Rust_primitives.mk_u16 10)
      (Rust_primitives.mk_u16 11)
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2
      (Rust_primitives.mk_usize 3)
      four._1
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2
      (Rust_primitives.mk_usize 4)
      four._2
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2
      (Rust_primitives.mk_usize 5)
      four._3
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
      (seed_base: t_Array u8 (Rust_primitives.mk_usize 66))
    : (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION &
      t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION) =
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
      (Rust_primitives.mk_u16 0)
      (Rust_primitives.mk_u16 1)
      (Rust_primitives.mk_u16 2)
      (Rust_primitives.mk_u16 3)
  in
  let s1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s1
      (Rust_primitives.mk_usize 0)
      four._1
  in
  let s1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s1
      (Rust_primitives.mk_usize 1)
      four._2
  in
  let s1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s1
      (Rust_primitives.mk_usize 2)
      four._3
  in
  let s1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s1
      (Rust_primitives.mk_usize 3)
      four._4
  in
  let four:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_error_ring_elements #v_SIMDUnit
      #v_Shake256X4
      v_ETA
      seed_base
      (Rust_primitives.mk_u16 4)
      (Rust_primitives.mk_u16 5)
      (Rust_primitives.mk_u16 6)
      (Rust_primitives.mk_u16 7)
  in
  let s1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s1
      (Rust_primitives.mk_usize 4)
      four._1
  in
  let s1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s1
      (Rust_primitives.mk_usize 5)
      four._2
  in
  let s1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s1
      (Rust_primitives.mk_usize 6)
      four._3
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2
      (Rust_primitives.mk_usize 0)
      four._4
  in
  let four:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_error_ring_elements #v_SIMDUnit
      #v_Shake256X4
      v_ETA
      seed_base
      (Rust_primitives.mk_u16 8)
      (Rust_primitives.mk_u16 9)
      (Rust_primitives.mk_u16 10)
      (Rust_primitives.mk_u16 11)
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2
      (Rust_primitives.mk_usize 1)
      four._1
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2
      (Rust_primitives.mk_usize 2)
      four._2
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2
      (Rust_primitives.mk_usize 3)
      four._3
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2
      (Rust_primitives.mk_usize 4)
      four._4
  in
  let four:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Libcrux_ml_dsa.Sample.sample_four_error_ring_elements #v_SIMDUnit
      #v_Shake256X4
      v_ETA
      seed_base
      (Rust_primitives.mk_u16 12)
      (Rust_primitives.mk_u16 13)
      (Rust_primitives.mk_u16 14)
      (Rust_primitives.mk_u16 15)
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2
      (Rust_primitives.mk_usize 5)
      four._1
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2
      (Rust_primitives.mk_usize 6)
      four._2
  in
  let s2:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2
      (Rust_primitives.mk_usize 7)
      four._3
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
      (seed: t_Array u8 (Rust_primitives.mk_usize 66))
    : (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S1_DIMENSION &
      t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_S2_DIMENSION) =
  match
    (cast (v_S1_DIMENSION <: usize) <: u8), (cast (v_S2_DIMENSION <: usize) <: u8) <: (u8 & u8)
  with
  | 4, 4 ->
    sample_s1_and_s2_4_by_4_ #v_SIMDUnit #v_Shake256X4 v_ETA v_S1_DIMENSION v_S2_DIMENSION seed
  | 5, 6 ->
    sample_s1_and_s2_5_by_6_ #v_SIMDUnit #v_Shake256X4 v_ETA v_S1_DIMENSION v_S2_DIMENSION seed
  | 7, 8 ->
    sample_s1_and_s2_7_by_8_ #v_SIMDUnit #v_Shake256X4 v_ETA v_S1_DIMENSION v_S2_DIMENSION seed
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)
