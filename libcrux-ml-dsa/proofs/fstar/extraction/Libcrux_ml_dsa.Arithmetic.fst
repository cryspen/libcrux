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
      (v_DIMENSION: usize)
      (v_GAMMA2: i32)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (t: t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION)
     =
  let vector_low:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION
  =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__ZERO #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      v_DIMENSION
  in
  let vector_high:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION
  =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__ZERO #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      v_DIMENSION
  in
  let vector_high, vector_low:(t_Array
      (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION &
    t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      v_DIMENSION
      (fun temp_0_ temp_1_ ->
          let vector_high, vector_low:(t_Array
              (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION &
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (vector_high, vector_low
        <:
        (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION &
          t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION))
      (fun temp_0_ i ->
          let vector_high, vector_low:(t_Array
              (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION &
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION) =
            temp_0_
          in
          let i:usize = i in
          Rust_primitives.Hax.Folds.fold_range (sz 0)
            (Core.Slice.impl__len #v_SIMDUnit
                ((vector_low.[ sz 0 ]).Libcrux_ml_dsa.Polynomial.f_simd_units <: t_Slice v_SIMDUnit)
              <:
              usize)
            (fun temp_0_ temp_1_ ->
                let vector_high, vector_low:(t_Array
                    (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION &
                  t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION
                ) =
                  temp_0_
                in
                let _:usize = temp_1_ in
                true)
            (vector_high, vector_low
              <:
              (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION &
                t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION))
            (fun temp_0_ j ->
                let vector_high, vector_low:(t_Array
                    (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION &
                  t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION
                ) =
                  temp_0_
                in
                let j:usize = j in
                let low, high:(v_SIMDUnit & v_SIMDUnit) =
                  Libcrux_ml_dsa.Simd.Traits.f_decompose #v_SIMDUnit
                    #FStar.Tactics.Typeclasses.solve
                    v_GAMMA2
                    ((t.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                        .Libcrux_ml_dsa.Polynomial.f_simd_units.[ j ]
                      <:
                      v_SIMDUnit)
                in
                let vector_low:t_Array
                  (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION =
                  Rust_primitives.Hax.Monomorphized_update_at.update_at_usize vector_low
                    i
                    ({
                        (vector_low.[ i ]
                          <:
                          Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) with
                        Libcrux_ml_dsa.Polynomial.f_simd_units
                        =
                        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (vector_low.[ i
                            ]
                            <:
                            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                            .Libcrux_ml_dsa.Polynomial.f_simd_units
                          j
                          low
                        <:
                        t_Array v_SIMDUnit (sz 32)
                      }
                      <:
                      Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                in
                let vector_high:t_Array
                  (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION =
                  Rust_primitives.Hax.Monomorphized_update_at.update_at_usize vector_high
                    i
                    ({
                        (vector_high.[ i ]
                          <:
                          Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) with
                        Libcrux_ml_dsa.Polynomial.f_simd_units
                        =
                        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (vector_high.[ i
                            ]
                            <:
                            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                            .Libcrux_ml_dsa.Polynomial.f_simd_units
                          j
                          high
                        <:
                        t_Array v_SIMDUnit (sz 32)
                      }
                      <:
                      Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                in
                vector_high, vector_low
                <:
                (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION &
                  t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION
                ))
          <:
          (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION &
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION))
  in
  vector_low, vector_high
  <:
  (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION &
    t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION)

let power2round_vector
      (#v_SIMDUnit: Type0)
      (v_DIMENSION: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (t: t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION)
     =
  let t0:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__ZERO #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      v_DIMENSION
  in
  let t1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__ZERO #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      v_DIMENSION
  in
  let t0, t1:(t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION &
    t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION) =
    Rust_primitives.Hax.Folds.fold_enumerated_slice (t
        <:
        t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (fun temp_0_ temp_1_ ->
          let t0, t1:(t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
              v_DIMENSION &
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (t0, t1
        <:
        (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION &
          t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION))
      (fun temp_0_ temp_1_ ->
          let t0, t1:(t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
              v_DIMENSION &
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION) =
            temp_0_
          in
          let i, ring_element:(usize & Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          =
            temp_1_
          in
          Rust_primitives.Hax.Folds.fold_enumerated_slice (ring_element
                .Libcrux_ml_dsa.Polynomial.f_simd_units
              <:
              t_Slice v_SIMDUnit)
            (fun temp_0_ temp_1_ ->
                let t0, t1:(t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                    v_DIMENSION &
                  t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION
                ) =
                  temp_0_
                in
                let _:usize = temp_1_ in
                true)
            (t0, t1
              <:
              (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION &
                t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION))
            (fun temp_0_ temp_1_ ->
                let t0, t1:(t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                    v_DIMENSION &
                  t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION
                ) =
                  temp_0_
                in
                let j, simd_unit:(usize & v_SIMDUnit) = temp_1_ in
                let t0_unit, t1_unit:(v_SIMDUnit & v_SIMDUnit) =
                  Libcrux_ml_dsa.Simd.Traits.f_power2round #v_SIMDUnit
                    #FStar.Tactics.Typeclasses.solve
                    simd_unit
                in
                let t0:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                  v_DIMENSION =
                  Rust_primitives.Hax.Monomorphized_update_at.update_at_usize t0
                    i
                    ({
                        (t0.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) with
                        Libcrux_ml_dsa.Polynomial.f_simd_units
                        =
                        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (t0.[ i ]
                            <:
                            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                            .Libcrux_ml_dsa.Polynomial.f_simd_units
                          j
                          t0_unit
                        <:
                        t_Array v_SIMDUnit (sz 32)
                      }
                      <:
                      Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                in
                let t1:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                  v_DIMENSION =
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
                          t1_unit
                        <:
                        t_Array v_SIMDUnit (sz 32)
                      }
                      <:
                      Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                in
                t0, t1
                <:
                (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION &
                  t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION
                ))
          <:
          (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION &
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION))
  in
  t0, t1
  <:
  (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION &
    t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION)

let shift_left_then_reduce
      (#v_SIMDUnit: Type0)
      (v_SHIFT_BY: i32)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
     =
  let out:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    Libcrux_ml_dsa.Polynomial.impl__ZERO #v_SIMDUnit ()
  in
  let out:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    Rust_primitives.Hax.Folds.fold_enumerated_slice (re.Libcrux_ml_dsa.Polynomial.f_simd_units
        <:
        t_Slice v_SIMDUnit)
      (fun out temp_1_ ->
          let out:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit = out in
          let _:usize = temp_1_ in
          true)
      out
      (fun out temp_1_ ->
          let out:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit = out in
          let i, simd_unit:(usize & v_SIMDUnit) = temp_1_ in
          {
            out with
            Libcrux_ml_dsa.Polynomial.f_simd_units
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
                .Libcrux_ml_dsa.Polynomial.f_simd_units
              i
              (Libcrux_ml_dsa.Simd.Traits.f_shift_left_then_reduce #v_SIMDUnit
                  #FStar.Tactics.Typeclasses.solve
                  v_SHIFT_BY
                  simd_unit
                <:
                v_SIMDUnit)
            <:
            t_Array v_SIMDUnit (sz 32)
          }
          <:
          Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
  in
  out

let use_hint
      (#v_SIMDUnit: Type0)
      (v_DIMENSION: usize)
      (v_GAMMA2: i32)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (hint: t_Array (t_Array i32 (sz 256)) v_DIMENSION)
      (re_vector:
          t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION)
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
          let hint_simd:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
            Libcrux_ml_dsa.Polynomial.impl__from_i32_array #v_SIMDUnit (hint.[ i ] <: t_Slice i32)
          in
          Rust_primitives.Hax.Folds.fold_range (sz 0)
            (Core.Slice.impl__len #v_SIMDUnit
                ((result.[ sz 0 ]).Libcrux_ml_dsa.Polynomial.f_simd_units <: t_Slice v_SIMDUnit)
              <:
              usize)
            (fun result temp_1_ ->
                let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                  v_DIMENSION =
                  result
                in
                let _:usize = temp_1_ in
                true)
            result
            (fun result j ->
                let result:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                  v_DIMENSION =
                  result
                in
                let j:usize = j in
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
                  i
                  ({
                      (result.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) with
                      Libcrux_ml_dsa.Polynomial.f_simd_units
                      =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (result.[ i ]
                          <:
                          Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                          .Libcrux_ml_dsa.Polynomial.f_simd_units
                        j
                        (Libcrux_ml_dsa.Simd.Traits.f_use_hint #v_SIMDUnit
                            #FStar.Tactics.Typeclasses.solve
                            v_GAMMA2
                            ((re_vector.[ i ]
                                <:
                                Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                                .Libcrux_ml_dsa.Polynomial.f_simd_units.[ j ]
                              <:
                              v_SIMDUnit)
                            (hint_simd.Libcrux_ml_dsa.Polynomial.f_simd_units.[ j ] <: v_SIMDUnit)
                          <:
                          v_SIMDUnit)
                      <:
                      t_Array v_SIMDUnit (sz 32)
                    }
                    <:
                    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                <:
                t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION))
  in
  result

let vector_infinity_norm_exceeds
      (#v_SIMDUnit: Type0)
      (v_DIMENSION: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (vector: t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION)
      (bound: i32)
     =
  let exceeds:bool = false in
  let exceeds:bool =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Slice.Iter.t_Iter
            (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
          #FStar.Tactics.Typeclasses.solve
          (Core.Slice.impl__iter #(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
              (vector <: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
            <:
            Core.Slice.Iter.t_Iter (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
        <:
        Core.Slice.Iter.t_Iter (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      exceeds
      (fun exceeds ring_element ->
          let exceeds:bool = exceeds in
          let ring_element:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
            ring_element
          in
          exceeds ||
          (Libcrux_ml_dsa.Polynomial.impl__infinity_norm_exceeds #v_SIMDUnit ring_element bound
            <:
            bool))
  in
  exceeds

let make_hint
      (#v_SIMDUnit: Type0)
      (v_DIMENSION: usize)
      (v_GAMMA2: i32)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (low high: t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION)
     =
  let hint:t_Array (t_Array i32 (sz 256)) v_DIMENSION =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat 0l (sz 256) <: t_Array i32 (sz 256))
      v_DIMENSION
  in
  let true_hints:usize = sz 0 in
  let hint, true_hints:(t_Array (t_Array i32 (sz 256)) v_DIMENSION & usize) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      v_DIMENSION
      (fun temp_0_ temp_1_ ->
          let hint, true_hints:(t_Array (t_Array i32 (sz 256)) v_DIMENSION & usize) = temp_0_ in
          let _:usize = temp_1_ in
          true)
      (hint, true_hints <: (t_Array (t_Array i32 (sz 256)) v_DIMENSION & usize))
      (fun temp_0_ i ->
          let hint, true_hints:(t_Array (t_Array i32 (sz 256)) v_DIMENSION & usize) = temp_0_ in
          let i:usize = i in
          let hint_simd:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
            Libcrux_ml_dsa.Polynomial.impl__ZERO #v_SIMDUnit ()
          in
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
                  let one_hints_count, current_hint:(usize & v_SIMDUnit) =
                    Libcrux_ml_dsa.Simd.Traits.f_compute_hint #v_SIMDUnit
                      #FStar.Tactics.Typeclasses.solve
                      v_GAMMA2
                      ((low.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                          .Libcrux_ml_dsa.Polynomial.f_simd_units.[ j ]
                        <:
                        v_SIMDUnit)
                      ((high.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                          .Libcrux_ml_dsa.Polynomial.f_simd_units.[ j ]
                        <:
                        v_SIMDUnit)
                  in
                  let hint_simd:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
                    {
                      hint_simd with
                      Libcrux_ml_dsa.Polynomial.f_simd_units
                      =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize hint_simd
                          .Libcrux_ml_dsa.Polynomial.f_simd_units
                        j
                        current_hint
                    }
                    <:
                    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit
                  in
                  let true_hints:usize = true_hints +! one_hints_count in
                  hint_simd, true_hints
                  <:
                  (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit & usize))
          in
          let hint:t_Array (t_Array i32 (sz 256)) v_DIMENSION =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize hint
              i
              (Libcrux_ml_dsa.Polynomial.impl__to_i32_array #v_SIMDUnit hint_simd
                <:
                t_Array i32 (sz 256))
          in
          hint, true_hints <: (t_Array (t_Array i32 (sz 256)) v_DIMENSION & usize))
  in
  hint, true_hints <: (t_Array (t_Array i32 (sz 256)) v_DIMENSION & usize)
