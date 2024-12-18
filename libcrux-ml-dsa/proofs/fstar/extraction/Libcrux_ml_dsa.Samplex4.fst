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

let matrix_A_4_by_4_
      (#v_SIMDUnit #v_Shake128: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128)
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
  let rand_stack:(t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
    t_Array u8 (sz 840)) =
    Rust_primitives.Hax.repeat 0uy (sz 840),
    Rust_primitives.Hax.repeat 0uy (sz 840),
    Rust_primitives.Hax.repeat 0uy (sz 840),
    Rust_primitives.Hax.repeat 0uy (sz 840)
    <:
    (t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840))
  in
  let tmp_stack:t_Array (t_Array i32 (sz 263)) (sz 4) =
    let list =
      [
        Rust_primitives.Hax.repeat 0l (sz 263);
        Rust_primitives.Hax.repeat 0l (sz 263);
        Rust_primitives.Hax.repeat 0l (sz 263);
        Rust_primitives.Hax.repeat 0l (sz 263)
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
    Rust_primitives.Hax.array_of_list 4 list
  in
  let tmp0, tmp1, tmp2:(t_Array
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      v_ROWS_IN_A &
    (t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840)) &
    t_Array (t_Array i32 (sz 263)) (sz 4)) =
    Libcrux_ml_dsa.Sample.sample_up_to_four_ring_elements #v_SIMDUnit #v_Shake128 v_ROWS_IN_A
      v_COLUMNS_IN_A seed v_A rand_stack tmp_stack
      (let list =
          [
            0uy, 0uy <: (u8 & u8);
            0uy, 1uy <: (u8 & u8);
            0uy, 2uy <: (u8 & u8);
            0uy, 3uy <: (u8 & u8)
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list) (sz 4)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    tmp0
  in
  let rand_stack:(t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
    t_Array u8 (sz 840)) =
    tmp1
  in
  let tmp_stack:t_Array (t_Array i32 (sz 263)) (sz 4) = tmp2 in
  let _:Prims.unit = () in
  let tmp0, tmp1, tmp2:(t_Array
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      v_ROWS_IN_A &
    (t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840)) &
    t_Array (t_Array i32 (sz 263)) (sz 4)) =
    Libcrux_ml_dsa.Sample.sample_up_to_four_ring_elements #v_SIMDUnit #v_Shake128 v_ROWS_IN_A
      v_COLUMNS_IN_A seed v_A rand_stack tmp_stack
      (let list =
          [
            1uy, 0uy <: (u8 & u8);
            1uy, 1uy <: (u8 & u8);
            1uy, 2uy <: (u8 & u8);
            1uy, 3uy <: (u8 & u8)
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list) (sz 4)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    tmp0
  in
  let rand_stack:(t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
    t_Array u8 (sz 840)) =
    tmp1
  in
  let tmp_stack:t_Array (t_Array i32 (sz 263)) (sz 4) = tmp2 in
  let _:Prims.unit = () in
  let tmp0, tmp1, tmp2:(t_Array
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      v_ROWS_IN_A &
    (t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840)) &
    t_Array (t_Array i32 (sz 263)) (sz 4)) =
    Libcrux_ml_dsa.Sample.sample_up_to_four_ring_elements #v_SIMDUnit #v_Shake128 v_ROWS_IN_A
      v_COLUMNS_IN_A seed v_A rand_stack tmp_stack
      (let list =
          [
            2uy, 0uy <: (u8 & u8);
            2uy, 1uy <: (u8 & u8);
            2uy, 2uy <: (u8 & u8);
            2uy, 3uy <: (u8 & u8)
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list) (sz 4)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    tmp0
  in
  let rand_stack:(t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
    t_Array u8 (sz 840)) =
    tmp1
  in
  let tmp_stack:t_Array (t_Array i32 (sz 263)) (sz 4) = tmp2 in
  let _:Prims.unit = () in
  let tmp0, tmp1, tmp2:(t_Array
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      v_ROWS_IN_A &
    (t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840)) &
    t_Array (t_Array i32 (sz 263)) (sz 4)) =
    Libcrux_ml_dsa.Sample.sample_up_to_four_ring_elements #v_SIMDUnit #v_Shake128 v_ROWS_IN_A
      v_COLUMNS_IN_A seed v_A rand_stack tmp_stack
      (let list =
          [
            3uy, 0uy <: (u8 & u8);
            3uy, 1uy <: (u8 & u8);
            3uy, 2uy <: (u8 & u8);
            3uy, 3uy <: (u8 & u8)
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list) (sz 4)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    tmp0
  in
  let rand_stack:(t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
    t_Array u8 (sz 840)) =
    tmp1
  in
  let tmp_stack:t_Array (t_Array i32 (sz 263)) (sz 4) = tmp2 in
  let _:Prims.unit = () in
  v_A

let matrix_A_6_by_5_
      (#v_SIMDUnit #v_Shake128: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128)
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
  let rand_stack:(t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
    t_Array u8 (sz 840)) =
    Rust_primitives.Hax.repeat 0uy (sz 840),
    Rust_primitives.Hax.repeat 0uy (sz 840),
    Rust_primitives.Hax.repeat 0uy (sz 840),
    Rust_primitives.Hax.repeat 0uy (sz 840)
    <:
    (t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840))
  in
  let tmp_stack:t_Array (t_Array i32 (sz 263)) (sz 4) =
    let list =
      [
        Rust_primitives.Hax.repeat 0l (sz 263);
        Rust_primitives.Hax.repeat 0l (sz 263);
        Rust_primitives.Hax.repeat 0l (sz 263);
        Rust_primitives.Hax.repeat 0l (sz 263)
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
    Rust_primitives.Hax.array_of_list 4 list
  in
  let tmp0, tmp1, tmp2:(t_Array
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      v_ROWS_IN_A &
    (t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840)) &
    t_Array (t_Array i32 (sz 263)) (sz 4)) =
    Libcrux_ml_dsa.Sample.sample_up_to_four_ring_elements #v_SIMDUnit #v_Shake128 v_ROWS_IN_A
      v_COLUMNS_IN_A seed v_A rand_stack tmp_stack
      (let list =
          [
            0uy, 0uy <: (u8 & u8);
            0uy, 1uy <: (u8 & u8);
            0uy, 2uy <: (u8 & u8);
            0uy, 3uy <: (u8 & u8)
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list) (sz 4)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    tmp0
  in
  let rand_stack:(t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
    t_Array u8 (sz 840)) =
    tmp1
  in
  let tmp_stack:t_Array (t_Array i32 (sz 263)) (sz 4) = tmp2 in
  let _:Prims.unit = () in
  let tmp0, tmp1, tmp2:(t_Array
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      v_ROWS_IN_A &
    (t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840)) &
    t_Array (t_Array i32 (sz 263)) (sz 4)) =
    Libcrux_ml_dsa.Sample.sample_up_to_four_ring_elements #v_SIMDUnit #v_Shake128 v_ROWS_IN_A
      v_COLUMNS_IN_A seed v_A rand_stack tmp_stack
      (let list =
          [
            0uy, 4uy <: (u8 & u8);
            1uy, 0uy <: (u8 & u8);
            1uy, 1uy <: (u8 & u8);
            1uy, 2uy <: (u8 & u8)
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list) (sz 4)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    tmp0
  in
  let rand_stack:(t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
    t_Array u8 (sz 840)) =
    tmp1
  in
  let tmp_stack:t_Array (t_Array i32 (sz 263)) (sz 4) = tmp2 in
  let _:Prims.unit = () in
  let tmp0, tmp1, tmp2:(t_Array
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      v_ROWS_IN_A &
    (t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840)) &
    t_Array (t_Array i32 (sz 263)) (sz 4)) =
    Libcrux_ml_dsa.Sample.sample_up_to_four_ring_elements #v_SIMDUnit #v_Shake128 v_ROWS_IN_A
      v_COLUMNS_IN_A seed v_A rand_stack tmp_stack
      (let list =
          [
            1uy, 3uy <: (u8 & u8);
            1uy, 4uy <: (u8 & u8);
            2uy, 0uy <: (u8 & u8);
            2uy, 1uy <: (u8 & u8)
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list) (sz 4)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    tmp0
  in
  let rand_stack:(t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
    t_Array u8 (sz 840)) =
    tmp1
  in
  let tmp_stack:t_Array (t_Array i32 (sz 263)) (sz 4) = tmp2 in
  let _:Prims.unit = () in
  let tmp0, tmp1, tmp2:(t_Array
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      v_ROWS_IN_A &
    (t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840)) &
    t_Array (t_Array i32 (sz 263)) (sz 4)) =
    Libcrux_ml_dsa.Sample.sample_up_to_four_ring_elements #v_SIMDUnit #v_Shake128 v_ROWS_IN_A
      v_COLUMNS_IN_A seed v_A rand_stack tmp_stack
      (let list =
          [
            2uy, 2uy <: (u8 & u8);
            2uy, 3uy <: (u8 & u8);
            2uy, 4uy <: (u8 & u8);
            3uy, 0uy <: (u8 & u8)
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list) (sz 4)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    tmp0
  in
  let rand_stack:(t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
    t_Array u8 (sz 840)) =
    tmp1
  in
  let tmp_stack:t_Array (t_Array i32 (sz 263)) (sz 4) = tmp2 in
  let _:Prims.unit = () in
  let tmp0, tmp1, tmp2:(t_Array
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      v_ROWS_IN_A &
    (t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840)) &
    t_Array (t_Array i32 (sz 263)) (sz 4)) =
    Libcrux_ml_dsa.Sample.sample_up_to_four_ring_elements #v_SIMDUnit #v_Shake128 v_ROWS_IN_A
      v_COLUMNS_IN_A seed v_A rand_stack tmp_stack
      (let list =
          [
            3uy, 1uy <: (u8 & u8);
            3uy, 2uy <: (u8 & u8);
            3uy, 3uy <: (u8 & u8);
            3uy, 4uy <: (u8 & u8)
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list) (sz 4)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    tmp0
  in
  let rand_stack:(t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
    t_Array u8 (sz 840)) =
    tmp1
  in
  let tmp_stack:t_Array (t_Array i32 (sz 263)) (sz 4) = tmp2 in
  let _:Prims.unit = () in
  let tmp0, tmp1, tmp2:(t_Array
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      v_ROWS_IN_A &
    (t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840)) &
    t_Array (t_Array i32 (sz 263)) (sz 4)) =
    Libcrux_ml_dsa.Sample.sample_up_to_four_ring_elements #v_SIMDUnit #v_Shake128 v_ROWS_IN_A
      v_COLUMNS_IN_A seed v_A rand_stack tmp_stack
      (let list =
          [
            4uy, 0uy <: (u8 & u8);
            4uy, 1uy <: (u8 & u8);
            4uy, 2uy <: (u8 & u8);
            4uy, 3uy <: (u8 & u8)
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list) (sz 4)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    tmp0
  in
  let rand_stack:(t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
    t_Array u8 (sz 840)) =
    tmp1
  in
  let tmp_stack:t_Array (t_Array i32 (sz 263)) (sz 4) = tmp2 in
  let _:Prims.unit = () in
  let tmp0, tmp1, tmp2:(t_Array
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      v_ROWS_IN_A &
    (t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840)) &
    t_Array (t_Array i32 (sz 263)) (sz 4)) =
    Libcrux_ml_dsa.Sample.sample_up_to_four_ring_elements #v_SIMDUnit #v_Shake128 v_ROWS_IN_A
      v_COLUMNS_IN_A seed v_A rand_stack tmp_stack
      (let list =
          [
            4uy, 4uy <: (u8 & u8);
            5uy, 0uy <: (u8 & u8);
            5uy, 1uy <: (u8 & u8);
            5uy, 2uy <: (u8 & u8)
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list) (sz 4)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    tmp0
  in
  let rand_stack:(t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
    t_Array u8 (sz 840)) =
    tmp1
  in
  let tmp_stack:t_Array (t_Array i32 (sz 263)) (sz 4) = tmp2 in
  let _:Prims.unit = () in
  let tmp0, tmp1, tmp2:(t_Array
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      v_ROWS_IN_A &
    (t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840)) &
    t_Array (t_Array i32 (sz 263)) (sz 4)) =
    Libcrux_ml_dsa.Sample.sample_up_to_four_ring_elements #v_SIMDUnit #v_Shake128 v_ROWS_IN_A
      v_COLUMNS_IN_A seed v_A rand_stack tmp_stack
      (let list =
          [
            5uy, 3uy <: (u8 & u8);
            5uy, 4uy <: (u8 & u8);
            5uy, 5uy <: (u8 & u8);
            5uy, 6uy <: (u8 & u8)
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list) (sz 2)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    tmp0
  in
  let rand_stack:(t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
    t_Array u8 (sz 840)) =
    tmp1
  in
  let tmp_stack:t_Array (t_Array i32 (sz 263)) (sz 4) = tmp2 in
  let _:Prims.unit = () in
  v_A

let matrix_A_8_by_7_
      (#v_SIMDUnit #v_Shake128: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128)
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
  let rand_stack:(t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
    t_Array u8 (sz 840)) =
    Rust_primitives.Hax.repeat 0uy (sz 840),
    Rust_primitives.Hax.repeat 0uy (sz 840),
    Rust_primitives.Hax.repeat 0uy (sz 840),
    Rust_primitives.Hax.repeat 0uy (sz 840)
    <:
    (t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840))
  in
  let tmp_stack:t_Array (t_Array i32 (sz 263)) (sz 4) =
    let list =
      [
        Rust_primitives.Hax.repeat 0l (sz 263);
        Rust_primitives.Hax.repeat 0l (sz 263);
        Rust_primitives.Hax.repeat 0l (sz 263);
        Rust_primitives.Hax.repeat 0l (sz 263)
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
    Rust_primitives.Hax.array_of_list 4 list
  in
  let tmp0, tmp1, tmp2:(t_Array
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      v_ROWS_IN_A &
    (t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840)) &
    t_Array (t_Array i32 (sz 263)) (sz 4)) =
    Libcrux_ml_dsa.Sample.sample_up_to_four_ring_elements #v_SIMDUnit #v_Shake128 v_ROWS_IN_A
      v_COLUMNS_IN_A seed v_A rand_stack tmp_stack
      (let list =
          [
            0uy, 0uy <: (u8 & u8);
            0uy, 1uy <: (u8 & u8);
            0uy, 2uy <: (u8 & u8);
            0uy, 3uy <: (u8 & u8)
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list) (sz 4)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    tmp0
  in
  let rand_stack:(t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
    t_Array u8 (sz 840)) =
    tmp1
  in
  let tmp_stack:t_Array (t_Array i32 (sz 263)) (sz 4) = tmp2 in
  let _:Prims.unit = () in
  let tmp0, tmp1, tmp2:(t_Array
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      v_ROWS_IN_A &
    (t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840)) &
    t_Array (t_Array i32 (sz 263)) (sz 4)) =
    Libcrux_ml_dsa.Sample.sample_up_to_four_ring_elements #v_SIMDUnit #v_Shake128 v_ROWS_IN_A
      v_COLUMNS_IN_A seed v_A rand_stack tmp_stack
      (let list =
          [
            0uy, 4uy <: (u8 & u8);
            0uy, 5uy <: (u8 & u8);
            0uy, 6uy <: (u8 & u8);
            1uy, 0uy <: (u8 & u8)
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list) (sz 4)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    tmp0
  in
  let rand_stack:(t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
    t_Array u8 (sz 840)) =
    tmp1
  in
  let tmp_stack:t_Array (t_Array i32 (sz 263)) (sz 4) = tmp2 in
  let _:Prims.unit = () in
  let tmp0, tmp1, tmp2:(t_Array
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      v_ROWS_IN_A &
    (t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840)) &
    t_Array (t_Array i32 (sz 263)) (sz 4)) =
    Libcrux_ml_dsa.Sample.sample_up_to_four_ring_elements #v_SIMDUnit #v_Shake128 v_ROWS_IN_A
      v_COLUMNS_IN_A seed v_A rand_stack tmp_stack
      (let list =
          [
            1uy, 1uy <: (u8 & u8);
            1uy, 2uy <: (u8 & u8);
            1uy, 3uy <: (u8 & u8);
            1uy, 4uy <: (u8 & u8)
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list) (sz 4)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    tmp0
  in
  let rand_stack:(t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
    t_Array u8 (sz 840)) =
    tmp1
  in
  let tmp_stack:t_Array (t_Array i32 (sz 263)) (sz 4) = tmp2 in
  let _:Prims.unit = () in
  let tmp0, tmp1, tmp2:(t_Array
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      v_ROWS_IN_A &
    (t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840)) &
    t_Array (t_Array i32 (sz 263)) (sz 4)) =
    Libcrux_ml_dsa.Sample.sample_up_to_four_ring_elements #v_SIMDUnit #v_Shake128 v_ROWS_IN_A
      v_COLUMNS_IN_A seed v_A rand_stack tmp_stack
      (let list =
          [
            1uy, 5uy <: (u8 & u8);
            1uy, 6uy <: (u8 & u8);
            2uy, 0uy <: (u8 & u8);
            2uy, 1uy <: (u8 & u8)
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list) (sz 4)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    tmp0
  in
  let rand_stack:(t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
    t_Array u8 (sz 840)) =
    tmp1
  in
  let tmp_stack:t_Array (t_Array i32 (sz 263)) (sz 4) = tmp2 in
  let _:Prims.unit = () in
  let tmp0, tmp1, tmp2:(t_Array
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      v_ROWS_IN_A &
    (t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840)) &
    t_Array (t_Array i32 (sz 263)) (sz 4)) =
    Libcrux_ml_dsa.Sample.sample_up_to_four_ring_elements #v_SIMDUnit #v_Shake128 v_ROWS_IN_A
      v_COLUMNS_IN_A seed v_A rand_stack tmp_stack
      (let list =
          [
            2uy, 2uy <: (u8 & u8);
            2uy, 3uy <: (u8 & u8);
            2uy, 4uy <: (u8 & u8);
            2uy, 5uy <: (u8 & u8)
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list) (sz 4)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    tmp0
  in
  let rand_stack:(t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
    t_Array u8 (sz 840)) =
    tmp1
  in
  let tmp_stack:t_Array (t_Array i32 (sz 263)) (sz 4) = tmp2 in
  let _:Prims.unit = () in
  let tmp0, tmp1, tmp2:(t_Array
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      v_ROWS_IN_A &
    (t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840)) &
    t_Array (t_Array i32 (sz 263)) (sz 4)) =
    Libcrux_ml_dsa.Sample.sample_up_to_four_ring_elements #v_SIMDUnit #v_Shake128 v_ROWS_IN_A
      v_COLUMNS_IN_A seed v_A rand_stack tmp_stack
      (let list =
          [
            2uy, 6uy <: (u8 & u8);
            3uy, 0uy <: (u8 & u8);
            3uy, 1uy <: (u8 & u8);
            3uy, 2uy <: (u8 & u8)
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list) (sz 4)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    tmp0
  in
  let rand_stack:(t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
    t_Array u8 (sz 840)) =
    tmp1
  in
  let tmp_stack:t_Array (t_Array i32 (sz 263)) (sz 4) = tmp2 in
  let _:Prims.unit = () in
  let tmp0, tmp1, tmp2:(t_Array
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      v_ROWS_IN_A &
    (t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840)) &
    t_Array (t_Array i32 (sz 263)) (sz 4)) =
    Libcrux_ml_dsa.Sample.sample_up_to_four_ring_elements #v_SIMDUnit #v_Shake128 v_ROWS_IN_A
      v_COLUMNS_IN_A seed v_A rand_stack tmp_stack
      (let list =
          [
            3uy, 3uy <: (u8 & u8);
            3uy, 4uy <: (u8 & u8);
            3uy, 5uy <: (u8 & u8);
            3uy, 6uy <: (u8 & u8)
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list) (sz 4)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    tmp0
  in
  let rand_stack:(t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
    t_Array u8 (sz 840)) =
    tmp1
  in
  let tmp_stack:t_Array (t_Array i32 (sz 263)) (sz 4) = tmp2 in
  let _:Prims.unit = () in
  let tmp0, tmp1, tmp2:(t_Array
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      v_ROWS_IN_A &
    (t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840)) &
    t_Array (t_Array i32 (sz 263)) (sz 4)) =
    Libcrux_ml_dsa.Sample.sample_up_to_four_ring_elements #v_SIMDUnit #v_Shake128 v_ROWS_IN_A
      v_COLUMNS_IN_A seed v_A rand_stack tmp_stack
      (let list =
          [
            4uy, 0uy <: (u8 & u8);
            4uy, 1uy <: (u8 & u8);
            4uy, 2uy <: (u8 & u8);
            4uy, 3uy <: (u8 & u8)
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list) (sz 4)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    tmp0
  in
  let rand_stack:(t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
    t_Array u8 (sz 840)) =
    tmp1
  in
  let tmp_stack:t_Array (t_Array i32 (sz 263)) (sz 4) = tmp2 in
  let _:Prims.unit = () in
  let tmp0, tmp1, tmp2:(t_Array
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      v_ROWS_IN_A &
    (t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840)) &
    t_Array (t_Array i32 (sz 263)) (sz 4)) =
    Libcrux_ml_dsa.Sample.sample_up_to_four_ring_elements #v_SIMDUnit #v_Shake128 v_ROWS_IN_A
      v_COLUMNS_IN_A seed v_A rand_stack tmp_stack
      (let list =
          [
            4uy, 4uy <: (u8 & u8);
            4uy, 5uy <: (u8 & u8);
            4uy, 6uy <: (u8 & u8);
            5uy, 0uy <: (u8 & u8)
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list) (sz 4)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    tmp0
  in
  let rand_stack:(t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
    t_Array u8 (sz 840)) =
    tmp1
  in
  let tmp_stack:t_Array (t_Array i32 (sz 263)) (sz 4) = tmp2 in
  let _:Prims.unit = () in
  let tmp0, tmp1, tmp2:(t_Array
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      v_ROWS_IN_A &
    (t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840)) &
    t_Array (t_Array i32 (sz 263)) (sz 4)) =
    Libcrux_ml_dsa.Sample.sample_up_to_four_ring_elements #v_SIMDUnit #v_Shake128 v_ROWS_IN_A
      v_COLUMNS_IN_A seed v_A rand_stack tmp_stack
      (let list =
          [
            5uy, 1uy <: (u8 & u8);
            5uy, 2uy <: (u8 & u8);
            5uy, 3uy <: (u8 & u8);
            5uy, 4uy <: (u8 & u8)
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list) (sz 4)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    tmp0
  in
  let rand_stack:(t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
    t_Array u8 (sz 840)) =
    tmp1
  in
  let tmp_stack:t_Array (t_Array i32 (sz 263)) (sz 4) = tmp2 in
  let _:Prims.unit = () in
  let tmp0, tmp1, tmp2:(t_Array
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      v_ROWS_IN_A &
    (t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840)) &
    t_Array (t_Array i32 (sz 263)) (sz 4)) =
    Libcrux_ml_dsa.Sample.sample_up_to_four_ring_elements #v_SIMDUnit #v_Shake128 v_ROWS_IN_A
      v_COLUMNS_IN_A seed v_A rand_stack tmp_stack
      (let list =
          [
            5uy, 5uy <: (u8 & u8);
            5uy, 6uy <: (u8 & u8);
            6uy, 0uy <: (u8 & u8);
            6uy, 1uy <: (u8 & u8)
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list) (sz 4)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    tmp0
  in
  let rand_stack:(t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
    t_Array u8 (sz 840)) =
    tmp1
  in
  let tmp_stack:t_Array (t_Array i32 (sz 263)) (sz 4) = tmp2 in
  let _:Prims.unit = () in
  let tmp0, tmp1, tmp2:(t_Array
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      v_ROWS_IN_A &
    (t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840)) &
    t_Array (t_Array i32 (sz 263)) (sz 4)) =
    Libcrux_ml_dsa.Sample.sample_up_to_four_ring_elements #v_SIMDUnit #v_Shake128 v_ROWS_IN_A
      v_COLUMNS_IN_A seed v_A rand_stack tmp_stack
      (let list =
          [
            6uy, 2uy <: (u8 & u8);
            6uy, 3uy <: (u8 & u8);
            6uy, 4uy <: (u8 & u8);
            6uy, 5uy <: (u8 & u8)
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list) (sz 4)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    tmp0
  in
  let rand_stack:(t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
    t_Array u8 (sz 840)) =
    tmp1
  in
  let tmp_stack:t_Array (t_Array i32 (sz 263)) (sz 4) = tmp2 in
  let _:Prims.unit = () in
  let tmp0, tmp1, tmp2:(t_Array
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      v_ROWS_IN_A &
    (t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840)) &
    t_Array (t_Array i32 (sz 263)) (sz 4)) =
    Libcrux_ml_dsa.Sample.sample_up_to_four_ring_elements #v_SIMDUnit #v_Shake128 v_ROWS_IN_A
      v_COLUMNS_IN_A seed v_A rand_stack tmp_stack
      (let list =
          [
            6uy, 6uy <: (u8 & u8);
            7uy, 0uy <: (u8 & u8);
            7uy, 1uy <: (u8 & u8);
            7uy, 2uy <: (u8 & u8)
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list) (sz 4)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    tmp0
  in
  let rand_stack:(t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
    t_Array u8 (sz 840)) =
    tmp1
  in
  let tmp_stack:t_Array (t_Array i32 (sz 263)) (sz 4) = tmp2 in
  let _:Prims.unit = () in
  let tmp0, tmp1, tmp2:(t_Array
      (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
      v_ROWS_IN_A &
    (t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840)) &
    t_Array (t_Array i32 (sz 263)) (sz 4)) =
    Libcrux_ml_dsa.Sample.sample_up_to_four_ring_elements #v_SIMDUnit #v_Shake128 v_ROWS_IN_A
      v_COLUMNS_IN_A seed v_A rand_stack tmp_stack
      (let list =
          [
            7uy, 3uy <: (u8 & u8);
            7uy, 4uy <: (u8 & u8);
            7uy, 5uy <: (u8 & u8);
            7uy, 6uy <: (u8 & u8)
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list) (sz 4)
  in
  let v_A:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    tmp0
  in
  let rand_stack:(t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
    t_Array u8 (sz 840)) =
    tmp1
  in
  let tmp_stack:t_Array (t_Array i32 (sz 263)) (sz 4) = tmp2 in
  let _:Prims.unit = () in
  v_A

let matrix_A_generic
      (#v_SIMDUnit #v_Shake128: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128)
      (seed: t_Array u8 (sz 34))
     =
  match
    (cast (v_ROWS_IN_A <: usize) <: u8), (cast (v_COLUMNS_IN_A <: usize) <: u8) <: (u8 & u8)
  with
  | 4uy, 4uy -> matrix_A_4_by_4_ #v_SIMDUnit #v_Shake128 v_ROWS_IN_A v_COLUMNS_IN_A seed
  | 6uy, 5uy -> matrix_A_6_by_5_ #v_SIMDUnit #v_Shake128 v_ROWS_IN_A v_COLUMNS_IN_A seed
  | 8uy, 7uy -> matrix_A_8_by_7_ #v_SIMDUnit #v_Shake128 v_ROWS_IN_A v_COLUMNS_IN_A seed
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
