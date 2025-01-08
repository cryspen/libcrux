module Libcrux_ml_dsa.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

let decompose_vector
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (dimension: usize)
      (gamma2: i32)
      (t low high: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
     =
  let high, low:(t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) &
    t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      dimension
      (fun temp_0_ temp_1_ ->
          let high, low:(t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) &
            t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (high, low
        <:
        (t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) &
          t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)))
      (fun temp_0_ i ->
          let high, low:(t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) &
            t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)) =
            temp_0_
          in
          let i:usize = i in
          Rust_primitives.Hax.Folds.fold_range (sz 0)
            (Core.Slice.impl__len #v_SIMDUnit
                ((low.[ sz 0 ]).Libcrux_ml_dsa.Polynomial.f_simd_units <: t_Slice v_SIMDUnit)
              <:
              usize)
            (fun temp_0_ temp_1_ ->
                let high, low:(t_Slice
                  (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) &
                  t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)) =
                  temp_0_
                in
                let _:usize = temp_1_ in
                true)
            (high, low
              <:
              (t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) &
                t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)))
            (fun temp_0_ j ->
                let high, low:(t_Slice
                  (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) &
                  t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)) =
                  temp_0_
                in
                let j:usize = j in
                let tmp0, tmp1:(v_SIMDUnit & v_SIMDUnit) =
                  Libcrux_ml_dsa.Simd.Traits.f_decompose #v_SIMDUnit
                    #FStar.Tactics.Typeclasses.solve
                    gamma2
                    ((t.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                        .Libcrux_ml_dsa.Polynomial.f_simd_units.[ j ]
                      <:
                      v_SIMDUnit)
                    ((low.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                        .Libcrux_ml_dsa.Polynomial.f_simd_units.[ j ]
                      <:
                      v_SIMDUnit)
                    ((high.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                        .Libcrux_ml_dsa.Polynomial.f_simd_units.[ j ]
                      <:
                      v_SIMDUnit)
                in
                let low:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
                  Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low
                    i
                    ({
                        (low.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) with
                        Libcrux_ml_dsa.Polynomial.f_simd_units
                        =
                        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (low.[ i ]
                            <:
                            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                            .Libcrux_ml_dsa.Polynomial.f_simd_units
                          j
                          tmp0
                        <:
                        t_Array v_SIMDUnit (sz 32)
                      }
                      <:
                      Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                in
                let high:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
                  Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high
                    i
                    ({
                        (high.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) with
                        Libcrux_ml_dsa.Polynomial.f_simd_units
                        =
                        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (high.[ i ]
                            <:
                            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                            .Libcrux_ml_dsa.Polynomial.f_simd_units
                          j
                          tmp1
                        <:
                        t_Array v_SIMDUnit (sz 32)
                      }
                      <:
                      Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                in
                high, low
                <:
                (t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) &
                  t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)))
          <:
          (t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) &
            t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)))
  in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  low, high
  <:
  (t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) &
    t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))

let power2round_vector
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (t t1: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
     =
  let t, t1:(t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) &
    t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) t
        <:
        usize)
      (fun temp_0_ temp_1_ ->
          let t, t1:(t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) &
            t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (t, t1
        <:
        (t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) &
          t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)))
      (fun temp_0_ i ->
          let t, t1:(t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) &
            t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)) =
            temp_0_
          in
          let i:usize = i in
          Rust_primitives.Hax.Folds.fold_range (sz 0)
            (Core.Slice.impl__len #v_SIMDUnit
                ((t.[ i ]).Libcrux_ml_dsa.Polynomial.f_simd_units <: t_Slice v_SIMDUnit)
              <:
              usize)
            (fun temp_0_ temp_1_ ->
                let t, t1:(t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) &
                  t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)) =
                  temp_0_
                in
                let _:usize = temp_1_ in
                true)
            (t, t1
              <:
              (t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) &
                t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)))
            (fun temp_0_ j ->
                let t, t1:(t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) &
                  t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)) =
                  temp_0_
                in
                let j:usize = j in
                let tmp0, tmp1:(v_SIMDUnit & v_SIMDUnit) =
                  Libcrux_ml_dsa.Simd.Traits.f_power2round #v_SIMDUnit
                    #FStar.Tactics.Typeclasses.solve
                    ((t.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                        .Libcrux_ml_dsa.Polynomial.f_simd_units.[ j ]
                      <:
                      v_SIMDUnit)
                    ((t1.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                        .Libcrux_ml_dsa.Polynomial.f_simd_units.[ j ]
                      <:
                      v_SIMDUnit)
                in
                let t:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
                  Rust_primitives.Hax.Monomorphized_update_at.update_at_usize t
                    i
                    ({
                        (t.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) with
                        Libcrux_ml_dsa.Polynomial.f_simd_units
                        =
                        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (t.[ i ]
                            <:
                            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                            .Libcrux_ml_dsa.Polynomial.f_simd_units
                          j
                          tmp0
                        <:
                        t_Array v_SIMDUnit (sz 32)
                      }
                      <:
                      Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                in
                let t1:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
                  Rust_primitives.Hax.Monomorphized_update_at.update_at_usize t1
                    i
                    ({
                        (t1.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) with
                        Libcrux_ml_dsa.Polynomial.f_simd_units
                        =
                        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (t1.[ i ]
                            <:
                            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                            .Libcrux_ml_dsa.Polynomial.f_simd_units
                          j
                          tmp1
                        <:
                        t_Array v_SIMDUnit (sz 32)
                      }
                      <:
                      Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                in
                t, t1
                <:
                (t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) &
                  t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)))
          <:
          (t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) &
            t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)))
  in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  t, t1
  <:
  (t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) &
    t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))

let shift_left_then_reduce
      (#v_SIMDUnit: Type0)
      (v_SHIFT_BY: i32)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
     =
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #v_SIMDUnit
          (re.Libcrux_ml_dsa.Polynomial.f_simd_units <: t_Slice v_SIMDUnit)
        <:
        usize)
      (fun re temp_1_ ->
          let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit = re in
          let _:usize = temp_1_ in
          true)
      re
      (fun re i ->
          let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit = re in
          let i:usize = i in
          {
            re with
            Libcrux_ml_dsa.Polynomial.f_simd_units
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                .Libcrux_ml_dsa.Polynomial.f_simd_units
              i
              (Libcrux_ml_dsa.Simd.Traits.f_shift_left_then_reduce #v_SIMDUnit
                  #FStar.Tactics.Typeclasses.solve
                  v_SHIFT_BY
                  (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ i ] <: v_SIMDUnit)
                <:
                v_SIMDUnit)
            <:
            t_Array v_SIMDUnit (sz 32)
          }
          <:
          Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
  in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  re

let use_hint
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (gamma2: i32)
      (hint: t_Slice (t_Array i32 (sz 256)))
      (re_vector: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
     =
  let re_vector:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          re_vector
        <:
        usize)
      (fun re_vector temp_1_ ->
          let re_vector:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
            re_vector
          in
          let _:usize = temp_1_ in
          true)
      re_vector
      (fun re_vector i ->
          let re_vector:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
            re_vector
          in
          let i:usize = i in
          let tmp:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
            Libcrux_ml_dsa.Polynomial.impl__zero #v_SIMDUnit ()
          in
          let tmp:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
            Libcrux_ml_dsa.Polynomial.impl__from_i32_array #v_SIMDUnit
              (hint.[ i ] <: t_Slice i32)
              tmp
          in
          let tmp:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
            Rust_primitives.Hax.Folds.fold_range (sz 0)
              (Core.Slice.impl__len #v_SIMDUnit
                  ((re_vector.[ sz 0 ]).Libcrux_ml_dsa.Polynomial.f_simd_units <: t_Slice v_SIMDUnit
                  )
                <:
                usize)
              (fun tmp temp_1_ ->
                  let tmp:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit = tmp in
                  let _:usize = temp_1_ in
                  true)
              tmp
              (fun tmp j ->
                  let tmp:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit = tmp in
                  let j:usize = j in
                  {
                    tmp with
                    Libcrux_ml_dsa.Polynomial.f_simd_units
                    =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize tmp
                        .Libcrux_ml_dsa.Polynomial.f_simd_units
                      j
                      (Libcrux_ml_dsa.Simd.Traits.f_use_hint #v_SIMDUnit
                          #FStar.Tactics.Typeclasses.solve
                          gamma2
                          ((re_vector.[ i ]
                              <:
                              Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                              .Libcrux_ml_dsa.Polynomial.f_simd_units.[ j ]
                            <:
                            v_SIMDUnit)
                          (tmp.Libcrux_ml_dsa.Polynomial.f_simd_units.[ j ] <: v_SIMDUnit)
                        <:
                        v_SIMDUnit)
                    <:
                    t_Array v_SIMDUnit (sz 32)
                  }
                  <:
                  Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          in
          let re_vector:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re_vector i tmp
          in
          re_vector)
  in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  re_vector

let vector_infinity_norm_exceeds
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (vector: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (bound: i32)
     =
  let result:bool = false in
  let result:bool =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Slice.Iter.t_Iter
            (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
          #FStar.Tactics.Typeclasses.solve
          (Core.Slice.impl__iter #(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
              vector
            <:
            Core.Slice.Iter.t_Iter (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
        <:
        Core.Slice.Iter.t_Iter (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      result
      (fun result ring_element ->
          let result:bool = result in
          let ring_element:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
            ring_element
          in
          result ||
          (Libcrux_ml_dsa.Polynomial.impl__infinity_norm_exceeds #v_SIMDUnit ring_element bound
            <:
            bool))
  in
  result

let make_hint
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (low high: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (gamma2: i32)
      (hint: t_Slice (t_Array i32 (sz 256)))
     =
  let true_hints:usize = sz 0 in
  let hint_simd:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    Libcrux_ml_dsa.Polynomial.impl__zero #v_SIMDUnit ()
  in
  let hint, hint_simd, true_hints:(t_Slice (t_Array i32 (sz 256)) &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    usize) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) low
        <:
        usize)
      (fun temp_0_ temp_1_ ->
          let hint, hint_simd, true_hints:(t_Slice (t_Array i32 (sz 256)) &
            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
            usize) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (hint, hint_simd, true_hints
        <:
        (t_Slice (t_Array i32 (sz 256)) &
          Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
          usize))
      (fun temp_0_ i ->
          let hint, hint_simd, true_hints:(t_Slice (t_Array i32 (sz 256)) &
            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
            usize) =
            temp_0_
          in
          let i:usize = i in
          let hint_simd, true_hints:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
            usize) =
            Rust_primitives.Hax.Folds.fold_range (sz 0)
              (Core.Slice.impl__len #v_SIMDUnit
                  (hint_simd.Libcrux_ml_dsa.Polynomial.f_simd_units <: t_Slice v_SIMDUnit)
                <:
                usize)
              (fun temp_0_ temp_1_ ->
                  let hint_simd, true_hints:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement
                    v_SIMDUnit &
                    usize) =
                    temp_0_
                  in
                  let _:usize = temp_1_ in
                  true)
              (hint_simd, true_hints
                <:
                (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit & usize))
              (fun temp_0_ j ->
                  let hint_simd, true_hints:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement
                    v_SIMDUnit &
                    usize) =
                    temp_0_
                  in
                  let j:usize = j in
                  let tmp0, out:(v_SIMDUnit & usize) =
                    Libcrux_ml_dsa.Simd.Traits.f_compute_hint #v_SIMDUnit
                      #FStar.Tactics.Typeclasses.solve
                      ((low.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                          .Libcrux_ml_dsa.Polynomial.f_simd_units.[ j ]
                        <:
                        v_SIMDUnit)
                      ((high.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                          .Libcrux_ml_dsa.Polynomial.f_simd_units.[ j ]
                        <:
                        v_SIMDUnit)
                      gamma2
                      (hint_simd.Libcrux_ml_dsa.Polynomial.f_simd_units.[ j ] <: v_SIMDUnit)
                  in
                  let hint_simd:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
                    {
                      hint_simd with
                      Libcrux_ml_dsa.Polynomial.f_simd_units
                      =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize hint_simd
                          .Libcrux_ml_dsa.Polynomial.f_simd_units
                        j
                        tmp0
                    }
                    <:
                    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit
                  in
                  let one_hints_count:usize = out in
                  let true_hints:usize = true_hints +! one_hints_count in
                  hint_simd, true_hints
                  <:
                  (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit & usize))
          in
          let hint:t_Slice (t_Array i32 (sz 256)) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize hint
              i
              (Libcrux_ml_dsa.Polynomial.impl__to_i32_array #v_SIMDUnit hint_simd
                <:
                t_Array i32 (sz 256))
          in
          hint, hint_simd, true_hints
          <:
          (t_Slice (t_Array i32 (sz 256)) &
            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
            usize))
  in
  let hax_temp_output:usize = true_hints in
  hint, hax_temp_output <: (t_Slice (t_Array i32 (sz 256)) & usize)
