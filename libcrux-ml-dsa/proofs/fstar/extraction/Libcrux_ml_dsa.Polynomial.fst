module Libcrux_ml_dsa.Polynomial
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

let impl__ZERO
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (_: Prims.unit)
     =
  {
    f_simd_units
    =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Simd.Traits.f_ZERO #v_SIMDUnit
          #FStar.Tactics.Typeclasses.solve
          ()
        <:
        v_SIMDUnit)
      (Rust_primitives.mk_usize 32)
  }
  <:
  t_PolynomialRingElement v_SIMDUnit

let impl__add
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (self rhs: t_PolynomialRingElement v_SIMDUnit)
     =
  let sum:t_PolynomialRingElement v_SIMDUnit = impl__ZERO #v_SIMDUnit () in
  let sum:t_PolynomialRingElement v_SIMDUnit =
    Rust_primitives.Hax.Folds.fold_range (Rust_primitives.mk_usize 0)
      (Core.Slice.impl__len #v_SIMDUnit (sum.f_simd_units <: t_Slice v_SIMDUnit) <: usize)
      (fun sum temp_1_ ->
          let sum:t_PolynomialRingElement v_SIMDUnit = sum in
          let _:usize = temp_1_ in
          true)
      sum
      (fun sum i ->
          let sum:t_PolynomialRingElement v_SIMDUnit = sum in
          let i:usize = i in
          {
            sum with
            f_simd_units
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize sum.f_simd_units
              i
              (Libcrux_ml_dsa.Simd.Traits.f_add #v_SIMDUnit
                  #FStar.Tactics.Typeclasses.solve
                  (self.f_simd_units.[ i ] <: v_SIMDUnit)
                  (rhs.f_simd_units.[ i ] <: v_SIMDUnit)
                <:
                v_SIMDUnit)
            <:
            t_Array v_SIMDUnit (Rust_primitives.mk_usize 32)
          }
          <:
          t_PolynomialRingElement v_SIMDUnit)
  in
  sum

let impl__from_i32_array
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (array: t_Slice i32)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #i32 array <: usize) >=.
            Rust_primitives.mk_usize 256
            <:
            bool)
      in
      ()
  in
  let array_chunks:Core.Slice.Iter.t_Chunks i32 =
    Core.Slice.impl__chunks #i32 array Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT
  in
  let result:t_PolynomialRingElement v_SIMDUnit = impl__ZERO #v_SIMDUnit () in
  let array_chunks, result:(Core.Slice.Iter.t_Chunks i32 & t_PolynomialRingElement v_SIMDUnit) =
    Rust_primitives.Hax.Folds.fold_range (Rust_primitives.mk_usize 0)
      Libcrux_ml_dsa.Simd.Traits.v_SIMD_UNITS_IN_RING_ELEMENT
      (fun temp_0_ temp_1_ ->
          let array_chunks, result:(Core.Slice.Iter.t_Chunks i32 &
            t_PolynomialRingElement v_SIMDUnit) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (array_chunks, result <: (Core.Slice.Iter.t_Chunks i32 & t_PolynomialRingElement v_SIMDUnit))
      (fun temp_0_ i ->
          let array_chunks, result:(Core.Slice.Iter.t_Chunks i32 &
            t_PolynomialRingElement v_SIMDUnit) =
            temp_0_
          in
          let i:usize = i in
          let tmp0, out:(Core.Slice.Iter.t_Chunks i32 & Core.Option.t_Option (t_Slice i32)) =
            Core.Iter.Traits.Iterator.f_next #(Core.Slice.Iter.t_Chunks i32)
              #FStar.Tactics.Typeclasses.solve
              array_chunks
          in
          let array_chunks:Core.Slice.Iter.t_Chunks i32 = tmp0 in
          array_chunks,
          ({
              result with
              f_simd_units
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_simd_units
                i
                (Libcrux_ml_dsa.Simd.Traits.f_from_coefficient_array #v_SIMDUnit
                    #FStar.Tactics.Typeclasses.solve
                    (Core.Option.impl__unwrap #(t_Slice i32) out <: t_Slice i32)
                  <:
                  v_SIMDUnit)
            }
            <:
            t_PolynomialRingElement v_SIMDUnit)
          <:
          (Core.Slice.Iter.t_Chunks i32 & t_PolynomialRingElement v_SIMDUnit))
  in
  result

let impl__infinity_norm_exceeds
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (self: t_PolynomialRingElement v_SIMDUnit)
      (bound: i32)
     =
  let exceeds:bool = false in
  let exceeds:bool =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(t_Array v_SIMDUnit
              (Rust_primitives.mk_usize 32))
          #FStar.Tactics.Typeclasses.solve
          self.f_simd_units
        <:
        Core.Array.Iter.t_IntoIter v_SIMDUnit (Rust_primitives.mk_usize 32))
      exceeds
      (fun exceeds simd_unit ->
          let exceeds:bool = exceeds in
          let simd_unit:v_SIMDUnit = simd_unit in
          exceeds |.
          (Libcrux_ml_dsa.Simd.Traits.f_infinity_norm_exceeds #v_SIMDUnit
              #FStar.Tactics.Typeclasses.solve
              simd_unit
              bound
            <:
            bool)
          <:
          bool)
  in
  exceeds

let impl__subtract
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (self rhs: t_PolynomialRingElement v_SIMDUnit)
     =
  let difference:t_PolynomialRingElement v_SIMDUnit = impl__ZERO #v_SIMDUnit () in
  let difference:t_PolynomialRingElement v_SIMDUnit =
    Rust_primitives.Hax.Folds.fold_range (Rust_primitives.mk_usize 0)
      (Core.Slice.impl__len #v_SIMDUnit (difference.f_simd_units <: t_Slice v_SIMDUnit) <: usize)
      (fun difference temp_1_ ->
          let difference:t_PolynomialRingElement v_SIMDUnit = difference in
          let _:usize = temp_1_ in
          true)
      difference
      (fun difference i ->
          let difference:t_PolynomialRingElement v_SIMDUnit = difference in
          let i:usize = i in
          {
            difference with
            f_simd_units
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize difference.f_simd_units
              i
              (Libcrux_ml_dsa.Simd.Traits.f_subtract #v_SIMDUnit
                  #FStar.Tactics.Typeclasses.solve
                  (self.f_simd_units.[ i ] <: v_SIMDUnit)
                  (rhs.f_simd_units.[ i ] <: v_SIMDUnit)
                <:
                v_SIMDUnit)
            <:
            t_Array v_SIMDUnit (Rust_primitives.mk_usize 32)
          }
          <:
          t_PolynomialRingElement v_SIMDUnit)
  in
  difference

let impl__to_i32_array
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (self: t_PolynomialRingElement v_SIMDUnit)
     =
  let result:t_Array i32 (Rust_primitives.mk_usize 256) =
    Rust_primitives.Hax.repeat (Rust_primitives.mk_i32 0) (Rust_primitives.mk_usize 256)
  in
  let result:t_Array i32 (Rust_primitives.mk_usize 256) =
    Rust_primitives.Hax.Folds.fold_enumerated_slice (self.f_simd_units <: t_Slice v_SIMDUnit)
      (fun result temp_1_ ->
          let result:t_Array i32 (Rust_primitives.mk_usize 256) = result in
          let _:usize = temp_1_ in
          true)
      result
      (fun result temp_1_ ->
          let result:t_Array i32 (Rust_primitives.mk_usize 256) = result in
          let i, simd_unit:(usize & v_SIMDUnit) = temp_1_ in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_range result
            ({
                Core.Ops.Range.f_start
                =
                i *! Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT <: usize;
                Core.Ops.Range.f_end
                =
                (i +! Rust_primitives.mk_usize 1 <: usize) *!
                Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT
                <:
                usize
              }
              <:
              Core.Ops.Range.t_Range usize)
            (Core.Slice.impl__copy_from_slice #i32
                (result.[ {
                      Core.Ops.Range.f_start
                      =
                      i *! Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT <: usize;
                      Core.Ops.Range.f_end
                      =
                      (i +! Rust_primitives.mk_usize 1 <: usize) *!
                      Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT
                      <:
                      usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice i32)
                (Libcrux_ml_dsa.Simd.Traits.f_to_coefficient_array #v_SIMDUnit
                    #FStar.Tactics.Typeclasses.solve
                    simd_unit
                  <:
                  t_Slice i32)
              <:
              t_Slice i32)
          <:
          t_Array i32 (Rust_primitives.mk_usize 256))
  in
  result
