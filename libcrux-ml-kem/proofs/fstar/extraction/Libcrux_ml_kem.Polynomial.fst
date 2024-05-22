module Libcrux_ml_kem.Polynomial
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let impl__ZERO
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_traits.t_Operations v_Vector)
      (_: Prims.unit)
     =
  { f_coefficients = Rust_primitives.Hax.repeat (Libcrux_traits.f_ZERO () <: v_Vector) (sz 16) }
  <:
  t_PolynomialRingElement v_Vector

let impl__add_error_reduce
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Libcrux_traits.t_Operations v_Vector)
      (self error: t_PolynomialRingElement v_Vector)
     =
  let self, hax_temp_output:t_PolynomialRingElement v_Vector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_VECTORS_IN_RING_ELEMENT
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      self
      (fun self j ->
          let self:t_PolynomialRingElement v_Vector = self in
          let j:usize = j in
          let coefficient_normal_form:v_Vector =
            Libcrux_traits.f_montgomery_multiply_by_constant (self.f_coefficients.[ j ] <: v_Vector)
              1441s
          in
          let self:t_PolynomialRingElement v_Vector =
            {
              self with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_coefficients
                j
                (Libcrux_traits.f_barrett_reduce (Libcrux_traits.f_add coefficient_normal_form
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
  self

let impl__add_message_error_reduce
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Libcrux_traits.t_Operations v_Vector)
      (self message result: t_PolynomialRingElement v_Vector)
     =
  let result:t_PolynomialRingElement v_Vector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_VECTORS_IN_RING_ELEMENT
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      result
      (fun result i ->
          let result:t_PolynomialRingElement v_Vector = result in
          let i:usize = i in
          let coefficient_normal_form:v_Vector =
            Libcrux_traits.f_montgomery_multiply_by_constant (result.f_coefficients.[ i ]
                <:
                v_Vector)
              1441s
          in
          let result:t_PolynomialRingElement v_Vector =
            {
              result with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_coefficients
                i
                (Libcrux_traits.f_barrett_reduce (Libcrux_traits.f_add coefficient_normal_form
                        (Libcrux_traits.f_add (self.f_coefficients.[ i ] <: v_Vector)
                            (message.f_coefficients.[ i ] <: v_Vector)
                          <:
                          v_Vector)
                      <:
                      v_Vector)
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
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Libcrux_traits.t_Operations v_Vector)
      (self error: t_PolynomialRingElement v_Vector)
     =
  let self, hax_temp_output:t_PolynomialRingElement v_Vector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_VECTORS_IN_RING_ELEMENT
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      self
      (fun self j ->
          let self:t_PolynomialRingElement v_Vector = self in
          let j:usize = j in
          let coefficient_normal_form:v_Vector =
            Libcrux_traits.f_to_standard_domain (self.f_coefficients.[ j ] <: v_Vector)
          in
          let self:t_PolynomialRingElement v_Vector =
            {
              self with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_coefficients
                j
                (Libcrux_traits.f_barrett_reduce (Libcrux_traits.f_add coefficient_normal_form
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
  self

let impl__add_to_ring_element
      (#v_Vector: Type)
      (v_K: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Libcrux_traits.t_Operations v_Vector)
      (self rhs: t_PolynomialRingElement v_Vector)
     =
  let self, hax_temp_output:t_PolynomialRingElement v_Vector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end
              =
              Core.Slice.impl__len (Rust_primitives.unsize self.f_coefficients <: t_Slice v_Vector)
              <:
              usize
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
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
              (Libcrux_traits.f_add (self.f_coefficients.[ i ] <: v_Vector)
                  (rhs.f_coefficients.[ i ] <: v_Vector)
                <:
                v_Vector)
            <:
            t_Array v_Vector (sz 16)
          }
          <:
          t_PolynomialRingElement v_Vector)
  in
  self

let impl__from_i16_array
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Libcrux_traits.t_Operations v_Vector)
      (a: t_Slice i16)
     =
  let result:t_PolynomialRingElement v_Vector = impl__ZERO () in
  let result:t_PolynomialRingElement v_Vector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_VECTORS_IN_RING_ELEMENT
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
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
              (Libcrux_traits.f_from_i16_array (a.[ {
                        Core.Ops.Range.f_start
                        =
                        i *! Libcrux_traits.v_FIELD_ELEMENTS_IN_VECTOR <: usize;
                        Core.Ops.Range.f_end
                        =
                        (i +! sz 1 <: usize) *! Libcrux_traits.v_FIELD_ELEMENTS_IN_VECTOR <: usize
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
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Libcrux_traits.t_Operations v_Vector)
      (self rhs: t_PolynomialRingElement v_Vector)
     =
  let out:t_PolynomialRingElement v_Vector = impl__ZERO () in
  let out:t_PolynomialRingElement v_Vector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_VECTORS_IN_RING_ELEMENT
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
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
              (Libcrux_traits.f_ntt_multiply (self.f_coefficients.[ i ] <: v_Vector)
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
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Libcrux_traits.t_Operations v_Vector)
      (self: t_PolynomialRingElement v_Vector)
     =
  let self, hax_temp_output:t_PolynomialRingElement v_Vector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_VECTORS_IN_RING_ELEMENT
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
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
              (Libcrux_traits.f_barrett_reduce (self.f_coefficients.[ i ] <: v_Vector) <: v_Vector)
            <:
            t_Array v_Vector (sz 16)
          }
          <:
          t_PolynomialRingElement v_Vector)
  in
  self

let impl__subtract_reduce
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Libcrux_traits.t_Operations v_Vector)
      (self b: t_PolynomialRingElement v_Vector)
     =
  let b:t_PolynomialRingElement v_Vector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_VECTORS_IN_RING_ELEMENT
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      b
      (fun b i ->
          let b:t_PolynomialRingElement v_Vector = b in
          let i:usize = i in
          let coefficient_normal_form:v_Vector =
            Libcrux_traits.f_montgomery_multiply_by_constant (b.f_coefficients.[ i ] <: v_Vector)
              1441s
          in
          let b:t_PolynomialRingElement v_Vector =
            {
              b with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize b.f_coefficients
                i
                (Libcrux_traits.f_barrett_reduce (Libcrux_traits.f_sub (self.f_coefficients.[ i ]
                          <:
                          v_Vector)
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
