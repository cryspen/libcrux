module Libcrux_ml_kem.Polynomial
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Vector.Traits in
  ()

let impl__ZERO
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (_: Prims.unit)
     =
  {
    f_coefficients
    =
    Rust_primitives.Hax.repeat (Libcrux_ml_kem.Vector.Traits.f_ZERO #v_Vector
          #FStar.Tactics.Typeclasses.solve
          ()
        <:
        v_Vector)
      (sz 16)
  }
  <:
  t_PolynomialRingElement v_Vector

let impl__add_error_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self error: t_PolynomialRingElement v_Vector)
     =
  let self:t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      v_VECTORS_IN_RING_ELEMENT
      (fun self temp_1_ ->
          let self:t_PolynomialRingElement v_Vector = self in
          let _:usize = temp_1_ in
          true)
      self
      (fun self j ->
          let self:t_PolynomialRingElement v_Vector = self in
          let j:usize = j in
          let coefficient_normal_form:v_Vector =
            Libcrux_ml_kem.Vector.Traits.f_montgomery_multiply_by_constant #v_Vector
              #FStar.Tactics.Typeclasses.solve
              (self.f_coefficients.[ j ] <: v_Vector)
              1441s
          in
          let self:t_PolynomialRingElement v_Vector =
            {
              self with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_coefficients
                j
                (Libcrux_ml_kem.Vector.Traits.f_barrett_reduce #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (Libcrux_ml_kem.Vector.Traits.f_add #v_Vector
                        #FStar.Tactics.Typeclasses.solve
                        coefficient_normal_form
                        (error.f_coefficients.[ j ] <: v_Vector)
                      <:
                      v_Vector)
                  <:
                  v_Vector)
            }
            <:
            t_PolynomialRingElement v_Vector
          in
          self)
  in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  self

let impl__add_message_error_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self message result: t_PolynomialRingElement v_Vector)
     =
  let result:t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      v_VECTORS_IN_RING_ELEMENT
      (fun result temp_1_ ->
          let result:t_PolynomialRingElement v_Vector = result in
          let _:usize = temp_1_ in
          true)
      result
      (fun result i ->
          let result:t_PolynomialRingElement v_Vector = result in
          let i:usize = i in
          let coefficient_normal_form:v_Vector =
            Libcrux_ml_kem.Vector.Traits.f_montgomery_multiply_by_constant #v_Vector
              #FStar.Tactics.Typeclasses.solve
              (result.f_coefficients.[ i ] <: v_Vector)
              1441s
          in
          let tmp:v_Vector =
            Libcrux_ml_kem.Vector.Traits.f_add #v_Vector
              #FStar.Tactics.Typeclasses.solve
              (self.f_coefficients.[ i ] <: v_Vector)
              (message.f_coefficients.[ i ] <: v_Vector)
          in
          let tmp:v_Vector =
            Libcrux_ml_kem.Vector.Traits.f_add #v_Vector
              #FStar.Tactics.Typeclasses.solve
              coefficient_normal_form
              tmp
          in
          let result:t_PolynomialRingElement v_Vector =
            {
              result with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_coefficients
                i
                (Libcrux_ml_kem.Vector.Traits.f_barrett_reduce #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    tmp
                  <:
                  v_Vector)
            }
            <:
            t_PolynomialRingElement v_Vector
          in
          result)
  in
  result

let impl__add_standard_error_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self error: t_PolynomialRingElement v_Vector)
     =
  let self:t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      v_VECTORS_IN_RING_ELEMENT
      (fun self temp_1_ ->
          let self:t_PolynomialRingElement v_Vector = self in
          let _:usize = temp_1_ in
          true)
      self
      (fun self j ->
          let self:t_PolynomialRingElement v_Vector = self in
          let j:usize = j in
          let coefficient_normal_form:v_Vector =
            Libcrux_ml_kem.Vector.Traits.to_standard_domain #v_Vector
              (self.f_coefficients.[ j ] <: v_Vector)
          in
          let self:t_PolynomialRingElement v_Vector =
            {
              self with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_coefficients
                j
                (Libcrux_ml_kem.Vector.Traits.f_barrett_reduce #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (Libcrux_ml_kem.Vector.Traits.f_add #v_Vector
                        #FStar.Tactics.Typeclasses.solve
                        coefficient_normal_form
                        (error.f_coefficients.[ j ] <: v_Vector)
                      <:
                      v_Vector)
                  <:
                  v_Vector)
            }
            <:
            t_PolynomialRingElement v_Vector
          in
          self)
  in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  self

let impl__add_to_ring_element
      (#v_Vector: Type0)
      (v_K: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self rhs: t_PolynomialRingElement v_Vector)
     =
  let self:t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #v_Vector (self.f_coefficients <: t_Slice v_Vector) <: usize)
      (fun self temp_1_ ->
          let self:t_PolynomialRingElement v_Vector = self in
          let _:usize = temp_1_ in
          true)
      self
      (fun self i ->
          let self:t_PolynomialRingElement v_Vector = self in
          let i:usize = i in
          {
            self with
            f_coefficients
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_coefficients
              i
              (Libcrux_ml_kem.Vector.Traits.f_add #v_Vector
                  #FStar.Tactics.Typeclasses.solve
                  (self.f_coefficients.[ i ] <: v_Vector)
                  (rhs.f_coefficients.[ i ] <: v_Vector)
                <:
                v_Vector)
            <:
            t_Array v_Vector (sz 16)
          }
          <:
          t_PolynomialRingElement v_Vector)
  in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  self

let impl__from_i16_array
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (a: t_Slice i16)
     =
  let result:t_PolynomialRingElement v_Vector = impl__ZERO #v_Vector () in
  let result:t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      v_VECTORS_IN_RING_ELEMENT
      (fun result temp_1_ ->
          let result:t_PolynomialRingElement v_Vector = result in
          let _:usize = temp_1_ in
          true)
      result
      (fun result i ->
          let result:t_PolynomialRingElement v_Vector = result in
          let i:usize = i in
          {
            result with
            f_coefficients
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_coefficients
              i
              (Libcrux_ml_kem.Vector.Traits.f_from_i16_array #v_Vector
                  #FStar.Tactics.Typeclasses.solve
                  (a.[ {
                        Core.Ops.Range.f_start = i *! sz 16 <: usize;
                        Core.Ops.Range.f_end = (i +! sz 1 <: usize) *! sz 16 <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice i16)
                <:
                v_Vector)
            <:
            t_Array v_Vector (sz 16)
          }
          <:
          t_PolynomialRingElement v_Vector)
  in
  result

let impl__ntt_multiply
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self rhs: t_PolynomialRingElement v_Vector)
     =
  let out:t_PolynomialRingElement v_Vector = impl__ZERO #v_Vector () in
  let out:t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      v_VECTORS_IN_RING_ELEMENT
      (fun out temp_1_ ->
          let out:t_PolynomialRingElement v_Vector = out in
          let _:usize = temp_1_ in
          true)
      out
      (fun out i ->
          let out:t_PolynomialRingElement v_Vector = out in
          let i:usize = i in
          {
            out with
            f_coefficients
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_coefficients
              i
              (Libcrux_ml_kem.Vector.Traits.f_ntt_multiply #v_Vector
                  #FStar.Tactics.Typeclasses.solve
                  (self.f_coefficients.[ i ] <: v_Vector)
                  (rhs.f_coefficients.[ i ] <: v_Vector)
                  (v_ZETAS_TIMES_MONTGOMERY_R.[ sz 64 +! (sz 4 *! i <: usize) <: usize ] <: i16)
                  (v_ZETAS_TIMES_MONTGOMERY_R.[ (sz 64 +! (sz 4 *! i <: usize) <: usize) +! sz 1
                      <:
                      usize ]
                    <:
                    i16)
                  (v_ZETAS_TIMES_MONTGOMERY_R.[ (sz 64 +! (sz 4 *! i <: usize) <: usize) +! sz 2
                      <:
                      usize ]
                    <:
                    i16)
                  (v_ZETAS_TIMES_MONTGOMERY_R.[ (sz 64 +! (sz 4 *! i <: usize) <: usize) +! sz 3
                      <:
                      usize ]
                    <:
                    i16)
                <:
                v_Vector)
            <:
            t_Array v_Vector (sz 16)
          }
          <:
          t_PolynomialRingElement v_Vector)
  in
  out

let impl__poly_barrett_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self: t_PolynomialRingElement v_Vector)
     =
  let self:t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      v_VECTORS_IN_RING_ELEMENT
      (fun self temp_1_ ->
          let self:t_PolynomialRingElement v_Vector = self in
          let _:usize = temp_1_ in
          true)
      self
      (fun self i ->
          let self:t_PolynomialRingElement v_Vector = self in
          let i:usize = i in
          {
            self with
            f_coefficients
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_coefficients
              i
              (Libcrux_ml_kem.Vector.Traits.f_barrett_reduce #v_Vector
                  #FStar.Tactics.Typeclasses.solve
                  (self.f_coefficients.[ i ] <: v_Vector)
                <:
                v_Vector)
            <:
            t_Array v_Vector (sz 16)
          }
          <:
          t_PolynomialRingElement v_Vector)
  in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  self

let impl__subtract_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self b: t_PolynomialRingElement v_Vector)
     =
  let b:t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      v_VECTORS_IN_RING_ELEMENT
      (fun b temp_1_ ->
          let b:t_PolynomialRingElement v_Vector = b in
          let _:usize = temp_1_ in
          true)
      b
      (fun b i ->
          let b:t_PolynomialRingElement v_Vector = b in
          let i:usize = i in
          let coefficient_normal_form:v_Vector =
            Libcrux_ml_kem.Vector.Traits.f_montgomery_multiply_by_constant #v_Vector
              #FStar.Tactics.Typeclasses.solve
              (b.f_coefficients.[ i ] <: v_Vector)
              1441s
          in
          let b:t_PolynomialRingElement v_Vector =
            {
              b with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize b.f_coefficients
                i
                (Libcrux_ml_kem.Vector.Traits.f_barrett_reduce #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (Libcrux_ml_kem.Vector.Traits.f_sub #v_Vector
                        #FStar.Tactics.Typeclasses.solve
                        (self.f_coefficients.[ i ] <: v_Vector)
                        coefficient_normal_form
                      <:
                      v_Vector)
                  <:
                  v_Vector)
            }
            <:
            t_PolynomialRingElement v_Vector
          in
          b)
  in
  b
