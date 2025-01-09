module Libcrux_ml_dsa.Polynomial
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1':
    #v_SIMDUnit: Type0 ->
    {| i1: Core.Clone.t_Clone v_SIMDUnit |} ->
    {| i2: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
  -> Core.Clone.t_Clone (t_PolynomialRingElement v_SIMDUnit)

let impl_1
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
     = impl_1' #v_SIMDUnit #i1 #i2

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2':
    #v_SIMDUnit: Type0 ->
    {| i1: Core.Marker.t_Copy v_SIMDUnit |} ->
    {| i2: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
  -> Core.Marker.t_Copy (t_PolynomialRingElement v_SIMDUnit)

let impl_2
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Marker.t_Copy v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
     = impl_2' #v_SIMDUnit #i1 #i2

let impl__from_i32_array
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (array: t_Slice i32)
      (result: t_PolynomialRingElement v_SIMDUnit)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #i32 array <: usize) >=. sz 256 <: bool)
      in
      ()
  in
  let result:t_PolynomialRingElement v_SIMDUnit =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      Libcrux_ml_dsa.Simd.Traits.v_SIMD_UNITS_IN_RING_ELEMENT
      (fun result temp_1_ ->
          let result:t_PolynomialRingElement v_SIMDUnit = result in
          let _:usize = temp_1_ in
          true)
      result
      (fun result i ->
          let result:t_PolynomialRingElement v_SIMDUnit = result in
          let i:usize = i in
          {
            result with
            f_simd_units
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_simd_units
              i
              (Libcrux_ml_dsa.Simd.Traits.f_from_coefficient_array #v_SIMDUnit
                  #FStar.Tactics.Typeclasses.solve
                  (array.[ {
                        Core.Ops.Range.f_start
                        =
                        i *! Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT <: usize;
                        Core.Ops.Range.f_end
                        =
                        (i +! sz 1 <: usize) *!
                        Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT
                        <:
                        usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice i32)
                  (result.f_simd_units.[ i ] <: v_SIMDUnit)
                <:
                v_SIMDUnit)
            <:
            t_Array v_SIMDUnit (sz 32)
          }
          <:
          t_PolynomialRingElement v_SIMDUnit)
  in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  result

let impl__zero
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (_: Prims.unit)
     =
  {
    f_simd_units
    =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Simd.Traits.f_zero #v_SIMDUnit
          #FStar.Tactics.Typeclasses.solve
          ()
        <:
        v_SIMDUnit)
      (sz 32)
  }
  <:
  t_PolynomialRingElement v_SIMDUnit

let impl__add
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (self rhs: t_PolynomialRingElement v_SIMDUnit)
     =
  let self:t_PolynomialRingElement v_SIMDUnit =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #v_SIMDUnit (self.f_simd_units <: t_Slice v_SIMDUnit) <: usize)
      (fun self temp_1_ ->
          let self:t_PolynomialRingElement v_SIMDUnit = self in
          let _:usize = temp_1_ in
          true)
      self
      (fun self i ->
          let self:t_PolynomialRingElement v_SIMDUnit = self in
          let i:usize = i in
          {
            self with
            f_simd_units
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_simd_units
              i
              (Libcrux_ml_dsa.Simd.Traits.f_add #v_SIMDUnit
                  #FStar.Tactics.Typeclasses.solve
                  (self.f_simd_units.[ i ] <: v_SIMDUnit)
                  (rhs.f_simd_units.[ i ] <: v_SIMDUnit)
                <:
                v_SIMDUnit)
            <:
            t_Array v_SIMDUnit (sz 32)
          }
          <:
          t_PolynomialRingElement v_SIMDUnit)
  in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  self

let impl__infinity_norm_exceeds
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (self: t_PolynomialRingElement v_SIMDUnit)
      (bound: i32)
     =
  let result:bool = false in
  let result:bool =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #v_SIMDUnit (self.f_simd_units <: t_Slice v_SIMDUnit) <: usize)
      (fun result temp_1_ ->
          let result:bool = result in
          let _:usize = temp_1_ in
          true)
      result
      (fun result i ->
          let result:bool = result in
          let i:usize = i in
          result ||
          (Libcrux_ml_dsa.Simd.Traits.f_infinity_norm_exceeds #v_SIMDUnit
              #FStar.Tactics.Typeclasses.solve
              (self.f_simd_units.[ i ] <: v_SIMDUnit)
              bound
            <:
            bool))
  in
  result

let impl__subtract
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (self rhs: t_PolynomialRingElement v_SIMDUnit)
     =
  let self:t_PolynomialRingElement v_SIMDUnit =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #v_SIMDUnit (self.f_simd_units <: t_Slice v_SIMDUnit) <: usize)
      (fun self temp_1_ ->
          let self:t_PolynomialRingElement v_SIMDUnit = self in
          let _:usize = temp_1_ in
          true)
      self
      (fun self i ->
          let self:t_PolynomialRingElement v_SIMDUnit = self in
          let i:usize = i in
          {
            self with
            f_simd_units
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_simd_units
              i
              (Libcrux_ml_dsa.Simd.Traits.f_subtract #v_SIMDUnit
                  #FStar.Tactics.Typeclasses.solve
                  (self.f_simd_units.[ i ] <: v_SIMDUnit)
                  (rhs.f_simd_units.[ i ] <: v_SIMDUnit)
                <:
                v_SIMDUnit)
            <:
            t_Array v_SIMDUnit (sz 32)
          }
          <:
          t_PolynomialRingElement v_SIMDUnit)
  in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  self

let impl__to_i32_array
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (self: t_PolynomialRingElement v_SIMDUnit)
     =
  let result:t_Array i32 (sz 256) = Rust_primitives.Hax.repeat 0l (sz 256) in
  let result:t_Array i32 (sz 256) =
    Rust_primitives.Hax.Folds.fold_enumerated_slice (self.f_simd_units <: t_Slice v_SIMDUnit)
      (fun result temp_1_ ->
          let result:t_Array i32 (sz 256) = result in
          let _:usize = temp_1_ in
          true)
      result
      (fun result temp_1_ ->
          let result:t_Array i32 (sz 256) = result in
          let i, simd_unit:(usize & v_SIMDUnit) = temp_1_ in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_range result
            ({
                Core.Ops.Range.f_start
                =
                i *! Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT <: usize;
                Core.Ops.Range.f_end
                =
                (i +! sz 1 <: usize) *! Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT
                <:
                usize
              }
              <:
              Core.Ops.Range.t_Range usize)
            (Libcrux_ml_dsa.Simd.Traits.f_to_coefficient_array #v_SIMDUnit
                #FStar.Tactics.Typeclasses.solve
                simd_unit
                (result.[ {
                      Core.Ops.Range.f_start
                      =
                      i *! Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT <: usize;
                      Core.Ops.Range.f_end
                      =
                      (i +! sz 1 <: usize) *! Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT
                      <:
                      usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice i32)
              <:
              t_Slice i32)
          <:
          t_Array i32 (sz 256))
  in
  result
