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

let matrix_flat
      (#v_SIMDUnit #v_Shake128: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128)
      (columns: usize)
      (seed: t_Slice u8)
      (matrix: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
     =
  let rand_stack0:t_Array u8 (sz 840) = Rust_primitives.Hax.repeat 0uy (sz 840) in
  let rand_stack1:t_Array u8 (sz 840) = Rust_primitives.Hax.repeat 0uy (sz 840) in
  let rand_stack2:t_Array u8 (sz 840) = Rust_primitives.Hax.repeat 0uy (sz 840) in
  let rand_stack3:t_Array u8 (sz 840) = Rust_primitives.Hax.repeat 0uy (sz 840) in
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
  let matrix, rand_stack0, rand_stack1, rand_stack2, rand_stack3, tmp_stack:(t_Slice
    (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) &
    t_Array u8 (sz 840) &
    t_Array u8 (sz 840) &
    t_Array u8 (sz 840) &
    t_Array u8 (sz 840) &
    t_Array (t_Array i32 (sz 263)) (sz 4)) =
    Rust_primitives.Hax.Folds.fold_range_step_by (sz 0)
      (Core.Slice.impl__len #(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) matrix
        <:
        usize)
      (sz 4)
      (fun temp_0_ temp_1_ ->
          let matrix, rand_stack0, rand_stack1, rand_stack2, rand_stack3, tmp_stack:(t_Slice
            (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) &
            t_Array u8 (sz 840) &
            t_Array u8 (sz 840) &
            t_Array u8 (sz 840) &
            t_Array u8 (sz 840) &
            t_Array (t_Array i32 (sz 263)) (sz 4)) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (matrix, rand_stack0, rand_stack1, rand_stack2, rand_stack3, tmp_stack
        <:
        (t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) &
          t_Array u8 (sz 840) &
          t_Array u8 (sz 840) &
          t_Array u8 (sz 840) &
          t_Array u8 (sz 840) &
          t_Array (t_Array i32 (sz 263)) (sz 4)))
      (fun temp_0_ start_index ->
          let matrix, rand_stack0, rand_stack1, rand_stack2, rand_stack3, tmp_stack:(t_Slice
            (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) &
            t_Array u8 (sz 840) &
            t_Array u8 (sz 840) &
            t_Array u8 (sz 840) &
            t_Array u8 (sz 840) &
            t_Array (t_Array i32 (sz 263)) (sz 4)) =
            temp_0_
          in
          let start_index:usize = start_index in
          let elements_requested:usize =
            if
              (start_index +! sz 4 <: usize) <=.
              (Core.Slice.impl__len #(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                  matrix
                <:
                usize)
            then sz 4
            else
              (Core.Slice.impl__len #(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                  matrix
                <:
                usize) -!
              start_index
          in
          let tmp0, tmp1, tmp2, tmp3, tmp4, tmp5:(t_Slice
            (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) &
            t_Array u8 (sz 840) &
            t_Array u8 (sz 840) &
            t_Array u8 (sz 840) &
            t_Array u8 (sz 840) &
            t_Array (t_Array i32 (sz 263)) (sz 4)) =
            Libcrux_ml_dsa.Sample.sample_up_to_four_ring_elements_flat #v_SIMDUnit #v_Shake128
              columns seed matrix rand_stack0 rand_stack1 rand_stack2 rand_stack3 tmp_stack
              start_index elements_requested
          in
          let matrix:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
            tmp0
          in
          let rand_stack0:t_Array u8 (sz 840) = tmp1 in
          let rand_stack1:t_Array u8 (sz 840) = tmp2 in
          let rand_stack2:t_Array u8 (sz 840) = tmp3 in
          let rand_stack3:t_Array u8 (sz 840) = tmp4 in
          let tmp_stack:t_Array (t_Array i32 (sz 263)) (sz 4) = tmp5 in
          let _:Prims.unit = () in
          matrix, rand_stack0, rand_stack1, rand_stack2, rand_stack3, tmp_stack
          <:
          (t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) &
            t_Array u8 (sz 840) &
            t_Array u8 (sz 840) &
            t_Array u8 (sz 840) &
            t_Array u8 (sz 840) &
            t_Array (t_Array i32 (sz 263)) (sz 4)))
  in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  matrix

let sample_s1_and_s2
      (#v_SIMDUnit #v_Shake256X4: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4)
      (eta: Libcrux_ml_dsa.Constants.t_Eta)
      (seed: t_Slice u8)
      (s1_s2: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
     =
  let len:usize =
    Core.Slice.impl__len #(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) s1_s2
  in
  let s1_s2:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (len /! sz 4 <: usize)
      (fun s1_s2 temp_1_ ->
          let s1_s2:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
            s1_s2
          in
          let _:usize = temp_1_ in
          true)
      s1_s2
      (fun s1_s2 i ->
          let s1_s2:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
            s1_s2
          in
          let i:usize = i in
          Libcrux_ml_dsa.Sample.sample_four_error_ring_elements #v_SIMDUnit
            #v_Shake256X4
            eta
            seed
            (4us *! (cast (i <: usize) <: u16) <: u16)
            s1_s2
          <:
          t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
  in
  let remainder:usize = len %! sz 4 in
  let s1_s2, hax_temp_output:(t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) &
    Prims.unit) =
    if remainder <>. sz 0
    then
      let s1_s2:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
        Libcrux_ml_dsa.Sample.sample_four_error_ring_elements #v_SIMDUnit
          #v_Shake256X4
          eta
          seed
          (cast (len -! remainder <: usize) <: u16)
          s1_s2
      in
      s1_s2, ()
      <:
      (t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) & Prims.unit)
    else
      s1_s2, ()
      <:
      (t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) & Prims.unit)
  in
  s1_s2
