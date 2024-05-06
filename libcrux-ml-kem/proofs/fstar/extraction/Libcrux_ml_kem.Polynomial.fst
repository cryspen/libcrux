module Libcrux_ml_kem.Polynomial
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let inv_ntt_layer_int_vec_step
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_traits.t_Operations v_Vector)
      (a b: v_Vector)
      (zeta_r: i32)
     =
  let a_minus_b:v_Vector = Libcrux_traits.f_sub b a in
  let a:v_Vector = Libcrux_traits.f_add a b in
  let b:v_Vector = Libcrux_traits.f_montgomery_multiply_fe_by_fer a_minus_b zeta_r in
  a, b <: (v_Vector & v_Vector)

let ntt_layer_7_int_vec_step
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_traits.t_Operations v_Vector)
      (a b: v_Vector)
     =
  let t:v_Vector = Libcrux_traits.f_multiply_by_constant b (-1600l) in
  let b:v_Vector = Libcrux_traits.f_sub a t in
  let a:v_Vector = Libcrux_traits.f_add a t in
  a, b <: (v_Vector & v_Vector)

let ntt_layer_int_vec_step
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_traits.t_Operations v_Vector)
      (a b: v_Vector)
      (zeta_r: i32)
     =
  let t:v_Vector = Libcrux_traits.f_montgomery_multiply_fe_by_fer b zeta_r in
  let b:v_Vector = Libcrux_traits.f_sub a t in
  let a:v_Vector = Libcrux_traits.f_add a t in
  a, b <: (v_Vector & v_Vector)

let impl__ZERO
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_traits.t_Operations v_Vector)
      (_: Prims.unit)
     =
  { f_coefficients = Rust_primitives.Hax.repeat (Libcrux_traits.f_ZERO () <: v_Vector) (sz 32) }
  <:
  t_PolynomialRingElement v_Vector

let impl__add_error_reduce
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Libcrux_traits.t_Operations v_Vector)
      (self result: t_PolynomialRingElement v_Vector)
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
      (fun result j ->
          let result:t_PolynomialRingElement v_Vector = result in
          let j:usize = j in
          let coefficient_normal_form:v_Vector =
            Libcrux_traits.f_montgomery_reduce (Libcrux_traits.f_multiply_by_constant (result
                      .f_coefficients.[ j ]
                    <:
                    v_Vector)
                  1441l
                <:
                v_Vector)
          in
          let result:t_PolynomialRingElement v_Vector =
            {
              result with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_coefficients
                j
                (Libcrux_traits.f_barrett_reduce (Libcrux_traits.f_add coefficient_normal_form
                        (self.f_coefficients.[ j ] <: v_Vector)
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
            Libcrux_traits.f_montgomery_reduce (Libcrux_traits.f_multiply_by_constant (result
                      .f_coefficients.[ i ]
                    <:
                    v_Vector)
                  1441l
                <:
                v_Vector)
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
      (self result: t_PolynomialRingElement v_Vector)
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
      (fun result j ->
          let result:t_PolynomialRingElement v_Vector = result in
          let j:usize = j in
          let coefficient_normal_form:v_Vector =
            Libcrux_traits.f_to_standard_domain (result.f_coefficients.[ j ] <: v_Vector)
          in
          let result:t_PolynomialRingElement v_Vector =
            {
              result with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_coefficients
                j
                (Libcrux_traits.f_barrett_reduce (Libcrux_traits.f_add coefficient_normal_form
                        (self.f_coefficients.[ j ] <: v_Vector)
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

let impl__add_to_ring_element
      (#v_Vector: Type)
      (v_K: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Libcrux_traits.t_Operations v_Vector)
      (self rhs: t_PolynomialRingElement v_Vector)
     =
  let self:t_PolynomialRingElement v_Vector =
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
            t_Array v_Vector (sz 32)
          }
          <:
          t_PolynomialRingElement v_Vector)
  in
  self

let impl__from_i32_array
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Libcrux_traits.t_Operations v_Vector)
      (a: t_Array i32 (sz 256))
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
              (Libcrux_traits.f_from_i32_array (Core.Result.impl__unwrap (Core.Convert.f_try_into (a.[
                              {
                                Core.Ops.Range.f_start
                                =
                                i *! Libcrux_traits.v_FIELD_ELEMENTS_IN_VECTOR <: usize;
                                Core.Ops.Range.f_end
                                =
                                (i +! sz 1 <: usize) *! Libcrux_traits.v_FIELD_ELEMENTS_IN_VECTOR
                                <:
                                usize
                              }
                              <:
                              Core.Ops.Range.t_Range usize ]
                            <:
                            t_Slice i32)
                        <:
                        Core.Result.t_Result (t_Array i32 (sz 8)) Core.Array.t_TryFromSliceError)
                    <:
                    t_Array i32 (sz 8))
                <:
                v_Vector)
            <:
            t_Array v_Vector (sz 32)
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
                  (v_ZETAS_TIMES_MONTGOMERY_R.[ sz 64 +! (sz 2 *! i <: usize) <: usize ] <: i32)
                  (v_ZETAS_TIMES_MONTGOMERY_R.[ (sz 64 +! (sz 2 *! i <: usize) <: usize) +! sz 1
                      <:
                      usize ]
                    <:
                    i32)
                <:
                v_Vector)
            <:
            t_Array v_Vector (sz 32)
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
  let self:t_PolynomialRingElement v_Vector =
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
            t_Array v_Vector (sz 32)
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
            Libcrux_traits.f_montgomery_reduce (Libcrux_traits.f_multiply_by_constant (b
                      .f_coefficients.[ i ]
                    <:
                    v_Vector)
                  1441l
                <:
                v_Vector)
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

let invert_ntt_at_layer_1_
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_traits.t_Operations v_Vector)
      (zeta_i: usize)
      (re: t_PolynomialRingElement v_Vector)
      (v__layer: usize)
     =
  let zeta_i:usize = zeta_i -! sz 1 in
  let re, zeta_i:(t_PolynomialRingElement v_Vector & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 32
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      (re, zeta_i <: (t_PolynomialRingElement v_Vector & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(t_PolynomialRingElement v_Vector & usize) = temp_0_ in
          let round:usize = round in
          let re:t_PolynomialRingElement v_Vector =
            {
              re with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_coefficients
                round
                (Libcrux_traits.f_inv_ntt_layer_1_step (re.f_coefficients.[ round ] <: v_Vector)
                    (v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i ] <: i32)
                    (v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i -! sz 1 <: usize ] <: i32)
                  <:
                  v_Vector)
            }
            <:
            t_PolynomialRingElement v_Vector
          in
          let zeta_i:usize = zeta_i -! sz 2 in
          re, zeta_i <: (t_PolynomialRingElement v_Vector & usize))
  in
  let zeta_i:usize = zeta_i +! sz 1 in
  let hax_temp_output:t_PolynomialRingElement v_Vector = re in
  zeta_i, hax_temp_output <: (usize & t_PolynomialRingElement v_Vector)

let invert_ntt_at_layer_2_
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_traits.t_Operations v_Vector)
      (zeta_i: usize)
      (re: t_PolynomialRingElement v_Vector)
      (v__layer: usize)
     =
  let re, zeta_i:(t_PolynomialRingElement v_Vector & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 32
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      (re, zeta_i <: (t_PolynomialRingElement v_Vector & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(t_PolynomialRingElement v_Vector & usize) = temp_0_ in
          let round:usize = round in
          let zeta_i:usize = zeta_i -! sz 1 in
          let re:t_PolynomialRingElement v_Vector =
            {
              re with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_coefficients
                round
                (Libcrux_traits.f_inv_ntt_layer_2_step (re.f_coefficients.[ round ] <: v_Vector)
                    (v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i ] <: i32)
                  <:
                  v_Vector)
            }
            <:
            t_PolynomialRingElement v_Vector
          in
          re, zeta_i <: (t_PolynomialRingElement v_Vector & usize))
  in
  let hax_temp_output:t_PolynomialRingElement v_Vector = re in
  zeta_i, hax_temp_output <: (usize & t_PolynomialRingElement v_Vector)

let invert_ntt_at_layer_3_plus
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_traits.t_Operations v_Vector)
      (zeta_i: usize)
      (re: t_PolynomialRingElement v_Vector)
      (layer: usize)
     =
  let step:usize = sz 1 <<! layer in
  let re, zeta_i:(t_PolynomialRingElement v_Vector & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 128 >>! layer <: usize
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      (re, zeta_i <: (t_PolynomialRingElement v_Vector & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(t_PolynomialRingElement v_Vector & usize) = temp_0_ in
          let round:usize = round in
          let zeta_i:usize = zeta_i -! sz 1 in
          let offset:usize = (round *! step <: usize) *! sz 2 in
          let offset_vec:usize = offset /! Libcrux_traits.v_FIELD_ELEMENTS_IN_VECTOR in
          let step_vec:usize = step /! Libcrux_traits.v_FIELD_ELEMENTS_IN_VECTOR in
          let re:t_PolynomialRingElement v_Vector =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                      Core.Ops.Range.f_start = offset_vec;
                      Core.Ops.Range.f_end = offset_vec +! step_vec <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize)
                <:
                Core.Ops.Range.t_Range usize)
              re
              (fun re j ->
                  let re:t_PolynomialRingElement v_Vector = re in
                  let j:usize = j in
                  let x, y:(v_Vector & v_Vector) =
                    inv_ntt_layer_int_vec_step (re.f_coefficients.[ j ] <: v_Vector)
                      (re.f_coefficients.[ j +! step_vec <: usize ] <: v_Vector)
                      (v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i ] <: i32)
                  in
                  let re:t_PolynomialRingElement v_Vector =
                    {
                      re with
                      f_coefficients
                      =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_coefficients
                        j
                        x
                    }
                    <:
                    t_PolynomialRingElement v_Vector
                  in
                  let re:t_PolynomialRingElement v_Vector =
                    {
                      re with
                      f_coefficients
                      =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_coefficients
                        (j +! step_vec <: usize)
                        y
                    }
                    <:
                    t_PolynomialRingElement v_Vector
                  in
                  re)
          in
          re, zeta_i <: (t_PolynomialRingElement v_Vector & usize))
  in
  let hax_temp_output:t_PolynomialRingElement v_Vector = re in
  zeta_i, hax_temp_output <: (usize & t_PolynomialRingElement v_Vector)

let ntt_at_layer_1_
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_traits.t_Operations v_Vector)
      (zeta_i: usize)
      (re: t_PolynomialRingElement v_Vector)
      (v__layer v__initial_coefficient_bound: usize)
     =
  let zeta_i:usize = zeta_i +! sz 1 in
  let re, zeta_i:(t_PolynomialRingElement v_Vector & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 32
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      (re, zeta_i <: (t_PolynomialRingElement v_Vector & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(t_PolynomialRingElement v_Vector & usize) = temp_0_ in
          let round:usize = round in
          let re:t_PolynomialRingElement v_Vector =
            {
              re with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_coefficients
                round
                (Libcrux_traits.f_ntt_layer_1_step (re.f_coefficients.[ round ] <: v_Vector)
                    (v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i ] <: i32)
                    (v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i +! sz 1 <: usize ] <: i32)
                  <:
                  v_Vector)
            }
            <:
            t_PolynomialRingElement v_Vector
          in
          let zeta_i:usize = zeta_i +! sz 2 in
          re, zeta_i <: (t_PolynomialRingElement v_Vector & usize))
  in
  let zeta_i:usize = zeta_i -! sz 1 in
  let hax_temp_output:t_PolynomialRingElement v_Vector = re in
  zeta_i, hax_temp_output <: (usize & t_PolynomialRingElement v_Vector)

let ntt_at_layer_2_
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_traits.t_Operations v_Vector)
      (zeta_i: usize)
      (re: t_PolynomialRingElement v_Vector)
      (v__layer v__initial_coefficient_bound: usize)
     =
  let re, zeta_i:(t_PolynomialRingElement v_Vector & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 32
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      (re, zeta_i <: (t_PolynomialRingElement v_Vector & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(t_PolynomialRingElement v_Vector & usize) = temp_0_ in
          let round:usize = round in
          let zeta_i:usize = zeta_i +! sz 1 in
          let re:t_PolynomialRingElement v_Vector =
            {
              re with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_coefficients
                round
                (Libcrux_traits.f_ntt_layer_2_step (re.f_coefficients.[ round ] <: v_Vector)
                    (v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i ] <: i32)
                  <:
                  v_Vector)
            }
            <:
            t_PolynomialRingElement v_Vector
          in
          re, zeta_i <: (t_PolynomialRingElement v_Vector & usize))
  in
  let hax_temp_output:t_PolynomialRingElement v_Vector = re in
  zeta_i, hax_temp_output <: (usize & t_PolynomialRingElement v_Vector)

let ntt_at_layer_3_plus
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_traits.t_Operations v_Vector)
      (zeta_i: usize)
      (re: t_PolynomialRingElement v_Vector)
      (layer v__initial_coefficient_bound: usize)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if ~.(layer >=. sz 3 <: bool)
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: layer >= 3"
              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let step:usize = sz 1 <<! layer in
  let re, zeta_i:(t_PolynomialRingElement v_Vector & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 128 >>! layer <: usize
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      (re, zeta_i <: (t_PolynomialRingElement v_Vector & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(t_PolynomialRingElement v_Vector & usize) = temp_0_ in
          let round:usize = round in
          let zeta_i:usize = zeta_i +! sz 1 in
          let offset:usize = (round *! step <: usize) *! sz 2 in
          let offset_vec:usize = offset /! Libcrux_traits.v_FIELD_ELEMENTS_IN_VECTOR in
          let step_vec:usize = step /! Libcrux_traits.v_FIELD_ELEMENTS_IN_VECTOR in
          let re:t_PolynomialRingElement v_Vector =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                      Core.Ops.Range.f_start = offset_vec;
                      Core.Ops.Range.f_end = offset_vec +! step_vec <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize)
                <:
                Core.Ops.Range.t_Range usize)
              re
              (fun re j ->
                  let re:t_PolynomialRingElement v_Vector = re in
                  let j:usize = j in
                  let x, y:(v_Vector & v_Vector) =
                    ntt_layer_int_vec_step (re.f_coefficients.[ j ] <: v_Vector)
                      (re.f_coefficients.[ j +! step_vec <: usize ] <: v_Vector)
                      (v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i ] <: i32)
                  in
                  let re:t_PolynomialRingElement v_Vector =
                    {
                      re with
                      f_coefficients
                      =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_coefficients
                        j
                        x
                    }
                    <:
                    t_PolynomialRingElement v_Vector
                  in
                  let re:t_PolynomialRingElement v_Vector =
                    {
                      re with
                      f_coefficients
                      =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_coefficients
                        (j +! step_vec <: usize)
                        y
                    }
                    <:
                    t_PolynomialRingElement v_Vector
                  in
                  re)
          in
          re, zeta_i <: (t_PolynomialRingElement v_Vector & usize))
  in
  let hax_temp_output:t_PolynomialRingElement v_Vector = re in
  zeta_i, hax_temp_output <: (usize & t_PolynomialRingElement v_Vector)

let ntt_at_layer_7_
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_traits.t_Operations v_Vector)
      (re: t_PolynomialRingElement v_Vector)
     =
  let step:usize = v_VECTORS_IN_RING_ELEMENT /! sz 2 in
  let re:t_PolynomialRingElement v_Vector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = step
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      re
      (fun re j ->
          let re:t_PolynomialRingElement v_Vector = re in
          let j:usize = j in
          let x, y:(v_Vector & v_Vector) =
            ntt_layer_7_int_vec_step (re.f_coefficients.[ j ] <: v_Vector)
              (re.f_coefficients.[ j +! step <: usize ] <: v_Vector)
          in
          let re:t_PolynomialRingElement v_Vector =
            {
              re with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_coefficients j x
            }
            <:
            t_PolynomialRingElement v_Vector
          in
          let re:t_PolynomialRingElement v_Vector =
            {
              re with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_coefficients
                (j +! step <: usize)
                y
            }
            <:
            t_PolynomialRingElement v_Vector
          in
          re)
  in
  re
