module Libcrux_ml_kem.Polynomial
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let impl__PolynomialRingElement__ZERO (_: Prims.unit) =
  {
    f_coefficients
    =
    Rust_primitives.Hax.repeat (Libcrux_ml_kem.Simd.Simd_trait.f_ZERO ()
        <:
        Libcrux_ml_kem.Simd.Portable.t_PortableVector)
      (sz 32)
  }
  <:
  t_PolynomialRingElement

let add_error_reduce (err result: t_PolynomialRingElement) =
  let result:t_PolynomialRingElement =
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
          let result:t_PolynomialRingElement = result in
          let j:usize = j in
          let coefficient_normal_form:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
            Libcrux_ml_kem.Simd.Simd_trait.f_montgomery_reduce (Libcrux_ml_kem.Simd.Simd_trait.f_multiply_by_constant
                  (result.f_coefficients.[ j ] <: Libcrux_ml_kem.Simd.Portable.t_PortableVector)
                  1441l
                <:
                Libcrux_ml_kem.Simd.Portable.t_PortableVector)
          in
          let result:t_PolynomialRingElement =
            {
              result with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_coefficients
                j
                (Libcrux_ml_kem.Simd.Simd_trait.f_barrett_reduce (Libcrux_ml_kem.Simd.Simd_trait.f_add
                        coefficient_normal_form
                        (err.f_coefficients.[ j ] <: Libcrux_ml_kem.Simd.Portable.t_PortableVector)
                      <:
                      Libcrux_ml_kem.Simd.Portable.t_PortableVector)
                  <:
                  Libcrux_ml_kem.Simd.Portable.t_PortableVector)
            }
            <:
            t_PolynomialRingElement
          in
          result)
  in
  result

let add_message_error_reduce (err message result: t_PolynomialRingElement) =
  let result:t_PolynomialRingElement =
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
          let result:t_PolynomialRingElement = result in
          let i:usize = i in
          let coefficient_normal_form:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
            Libcrux_ml_kem.Simd.Simd_trait.f_montgomery_reduce (Libcrux_ml_kem.Simd.Simd_trait.f_multiply_by_constant
                  (result.f_coefficients.[ i ] <: Libcrux_ml_kem.Simd.Portable.t_PortableVector)
                  1441l
                <:
                Libcrux_ml_kem.Simd.Portable.t_PortableVector)
          in
          let result:t_PolynomialRingElement =
            {
              result with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_coefficients
                i
                (Libcrux_ml_kem.Simd.Simd_trait.f_barrett_reduce (Libcrux_ml_kem.Simd.Simd_trait.f_add
                        coefficient_normal_form
                        (Libcrux_ml_kem.Simd.Simd_trait.f_add (err.f_coefficients.[ i ]
                              <:
                              Libcrux_ml_kem.Simd.Portable.t_PortableVector)
                            (message.f_coefficients.[ i ]
                              <:
                              Libcrux_ml_kem.Simd.Portable.t_PortableVector)
                          <:
                          Libcrux_ml_kem.Simd.Portable.t_PortableVector)
                      <:
                      Libcrux_ml_kem.Simd.Portable.t_PortableVector)
                  <:
                  Libcrux_ml_kem.Simd.Portable.t_PortableVector)
            }
            <:
            t_PolynomialRingElement
          in
          result)
  in
  result

let add_standard_error_reduce (err result: t_PolynomialRingElement) =
  let result:t_PolynomialRingElement =
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
          let result:t_PolynomialRingElement = result in
          let j:usize = j in
          let coefficient_normal_form:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
            Libcrux_ml_kem.Simd.Simd_trait.f_to_standard_domain (result.f_coefficients.[ j ]
                <:
                Libcrux_ml_kem.Simd.Portable.t_PortableVector)
          in
          let result:t_PolynomialRingElement =
            {
              result with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_coefficients
                j
                (Libcrux_ml_kem.Simd.Simd_trait.f_barrett_reduce (Libcrux_ml_kem.Simd.Simd_trait.f_add
                        coefficient_normal_form
                        (err.f_coefficients.[ j ] <: Libcrux_ml_kem.Simd.Portable.t_PortableVector)
                      <:
                      Libcrux_ml_kem.Simd.Portable.t_PortableVector)
                  <:
                  Libcrux_ml_kem.Simd.Portable.t_PortableVector)
            }
            <:
            t_PolynomialRingElement
          in
          result)
  in
  result

let add_to_ring_element (v_K: usize) (lhs rhs: t_PolynomialRingElement) =
  let lhs:t_PolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end
              =
              Core.Slice.impl__len (Rust_primitives.unsize lhs.f_coefficients
                  <:
                  t_Slice Libcrux_ml_kem.Simd.Portable.t_PortableVector)
              <:
              usize
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      lhs
      (fun lhs i ->
          let lhs:t_PolynomialRingElement = lhs in
          let i:usize = i in
          {
            lhs with
            f_coefficients
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize lhs.f_coefficients
              i
              (Libcrux_ml_kem.Simd.Simd_trait.f_add (lhs.f_coefficients.[ i ]
                    <:
                    Libcrux_ml_kem.Simd.Portable.t_PortableVector)
                  (rhs.f_coefficients.[ i ] <: Libcrux_ml_kem.Simd.Portable.t_PortableVector)
                <:
                Libcrux_ml_kem.Simd.Portable.t_PortableVector)
            <:
            t_Array Libcrux_ml_kem.Simd.Portable.t_PortableVector (sz 32)
          }
          <:
          t_PolynomialRingElement)
  in
  lhs

let from_i32_array (a: t_Array i32 (sz 256)) =
  let result:t_PolynomialRingElement = impl__PolynomialRingElement__ZERO () in
  let result:t_PolynomialRingElement =
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
          let result:t_PolynomialRingElement = result in
          let i:usize = i in
          {
            result with
            f_coefficients
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_coefficients
              i
              (Libcrux_ml_kem.Simd.Simd_trait.f_from_i32_array (Core.Result.impl__unwrap (Core.Convert.f_try_into
                          (a.[ {
                                Core.Ops.Range.f_start
                                =
                                i *! Libcrux_ml_kem.Simd.Simd_trait.f_FIELD_ELEMENTS_IN_VECTOR
                                <:
                                usize;
                                Core.Ops.Range.f_end
                                =
                                (i +! sz 1 <: usize) *!
                                Libcrux_ml_kem.Simd.Simd_trait.f_FIELD_ELEMENTS_IN_VECTOR
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
                Libcrux_ml_kem.Simd.Portable.t_PortableVector)
            <:
            t_Array Libcrux_ml_kem.Simd.Portable.t_PortableVector (sz 32)
          }
          <:
          t_PolynomialRingElement)
  in
  result

let inv_ntt_layer_int_vec_step (a b: Libcrux_ml_kem.Simd.Portable.t_PortableVector) (zeta_r: i32) =
  let a_minus_b:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
    Libcrux_ml_kem.Simd.Simd_trait.f_sub b a
  in
  let a:Libcrux_ml_kem.Simd.Portable.t_PortableVector = Libcrux_ml_kem.Simd.Simd_trait.f_add a b in
  let b:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
    Libcrux_ml_kem.Simd.Simd_trait.f_montgomery_multiply_fe_by_fer a_minus_b zeta_r
  in
  a, b
  <:
  (Libcrux_ml_kem.Simd.Portable.t_PortableVector & Libcrux_ml_kem.Simd.Portable.t_PortableVector)

let invert_ntt_at_layer_1_ (zeta_i: usize) (re: t_PolynomialRingElement) (v__layer: usize) =
  let zeta_i:usize = zeta_i -! sz 1 in
  let re, zeta_i:(t_PolynomialRingElement & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 32
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      (re, zeta_i <: (t_PolynomialRingElement & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(t_PolynomialRingElement & usize) = temp_0_ in
          let round:usize = round in
          let re:t_PolynomialRingElement =
            {
              re with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_coefficients
                round
                (Libcrux_ml_kem.Simd.Simd_trait.f_inv_ntt_layer_1_step (re.f_coefficients.[ round ]
                      <:
                      Libcrux_ml_kem.Simd.Portable.t_PortableVector)
                    (v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i ] <: i32)
                    (v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i -! sz 1 <: usize ] <: i32)
                  <:
                  Libcrux_ml_kem.Simd.Portable.t_PortableVector)
            }
            <:
            t_PolynomialRingElement
          in
          let zeta_i:usize = zeta_i -! sz 2 in
          re, zeta_i <: (t_PolynomialRingElement & usize))
  in
  let zeta_i:usize = zeta_i +! sz 1 in
  let hax_temp_output:t_PolynomialRingElement = re in
  zeta_i, hax_temp_output <: (usize & t_PolynomialRingElement)

let invert_ntt_at_layer_2_ (zeta_i: usize) (re: t_PolynomialRingElement) (v__layer: usize) =
  let re, zeta_i:(t_PolynomialRingElement & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 32
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      (re, zeta_i <: (t_PolynomialRingElement & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(t_PolynomialRingElement & usize) = temp_0_ in
          let round:usize = round in
          let zeta_i:usize = zeta_i -! sz 1 in
          let re:t_PolynomialRingElement =
            {
              re with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_coefficients
                round
                (Libcrux_ml_kem.Simd.Simd_trait.f_inv_ntt_layer_2_step (re.f_coefficients.[ round ]
                      <:
                      Libcrux_ml_kem.Simd.Portable.t_PortableVector)
                    (v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i ] <: i32)
                  <:
                  Libcrux_ml_kem.Simd.Portable.t_PortableVector)
            }
            <:
            t_PolynomialRingElement
          in
          re, zeta_i <: (t_PolynomialRingElement & usize))
  in
  let hax_temp_output:t_PolynomialRingElement = re in
  zeta_i, hax_temp_output <: (usize & t_PolynomialRingElement)

let invert_ntt_at_layer_3_plus (zeta_i: usize) (re: t_PolynomialRingElement) (layer: usize) =
  let step:usize = sz 1 <<! layer in
  let re, zeta_i:(t_PolynomialRingElement & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 128 >>! layer <: usize
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      (re, zeta_i <: (t_PolynomialRingElement & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(t_PolynomialRingElement & usize) = temp_0_ in
          let round:usize = round in
          let zeta_i:usize = zeta_i -! sz 1 in
          let offset:usize = (round *! step <: usize) *! sz 2 in
          let offset_vec:usize =
            offset /! Libcrux_ml_kem.Simd.Simd_trait.f_FIELD_ELEMENTS_IN_VECTOR
          in
          let step_vec:usize = step /! Libcrux_ml_kem.Simd.Simd_trait.f_FIELD_ELEMENTS_IN_VECTOR in
          let re:t_PolynomialRingElement =
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
                  let re:t_PolynomialRingElement = re in
                  let j:usize = j in
                  let x, y:(Libcrux_ml_kem.Simd.Portable.t_PortableVector &
                    Libcrux_ml_kem.Simd.Portable.t_PortableVector) =
                    inv_ntt_layer_int_vec_step (re.f_coefficients.[ j ]
                        <:
                        Libcrux_ml_kem.Simd.Portable.t_PortableVector)
                      (re.f_coefficients.[ j +! step_vec <: usize ]
                        <:
                        Libcrux_ml_kem.Simd.Portable.t_PortableVector)
                      (v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i ] <: i32)
                  in
                  let re:t_PolynomialRingElement =
                    {
                      re with
                      f_coefficients
                      =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_coefficients
                        j
                        x
                    }
                    <:
                    t_PolynomialRingElement
                  in
                  let re:t_PolynomialRingElement =
                    {
                      re with
                      f_coefficients
                      =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_coefficients
                        (j +! step_vec <: usize)
                        y
                    }
                    <:
                    t_PolynomialRingElement
                  in
                  re)
          in
          re, zeta_i <: (t_PolynomialRingElement & usize))
  in
  let hax_temp_output:t_PolynomialRingElement = re in
  zeta_i, hax_temp_output <: (usize & t_PolynomialRingElement)

let ntt_at_layer_1_
      (zeta_i: usize)
      (re: t_PolynomialRingElement)
      (v__layer v__initial_coefficient_bound: usize)
     =
  let zeta_i:usize = zeta_i +! sz 1 in
  let re, zeta_i:(t_PolynomialRingElement & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 32
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      (re, zeta_i <: (t_PolynomialRingElement & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(t_PolynomialRingElement & usize) = temp_0_ in
          let round:usize = round in
          let re:t_PolynomialRingElement =
            {
              re with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_coefficients
                round
                (Libcrux_ml_kem.Simd.Simd_trait.f_ntt_layer_1_step (re.f_coefficients.[ round ]
                      <:
                      Libcrux_ml_kem.Simd.Portable.t_PortableVector)
                    (v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i ] <: i32)
                    (v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i +! sz 1 <: usize ] <: i32)
                  <:
                  Libcrux_ml_kem.Simd.Portable.t_PortableVector)
            }
            <:
            t_PolynomialRingElement
          in
          let zeta_i:usize = zeta_i +! sz 2 in
          re, zeta_i <: (t_PolynomialRingElement & usize))
  in
  let zeta_i:usize = zeta_i -! sz 1 in
  let hax_temp_output:t_PolynomialRingElement = re in
  zeta_i, hax_temp_output <: (usize & t_PolynomialRingElement)

let ntt_at_layer_2_
      (zeta_i: usize)
      (re: t_PolynomialRingElement)
      (v__layer v__initial_coefficient_bound: usize)
     =
  let re, zeta_i:(t_PolynomialRingElement & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 32
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      (re, zeta_i <: (t_PolynomialRingElement & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(t_PolynomialRingElement & usize) = temp_0_ in
          let round:usize = round in
          let zeta_i:usize = zeta_i +! sz 1 in
          let re:t_PolynomialRingElement =
            {
              re with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_coefficients
                round
                (Libcrux_ml_kem.Simd.Simd_trait.f_ntt_layer_2_step (re.f_coefficients.[ round ]
                      <:
                      Libcrux_ml_kem.Simd.Portable.t_PortableVector)
                    (v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i ] <: i32)
                  <:
                  Libcrux_ml_kem.Simd.Portable.t_PortableVector)
            }
            <:
            t_PolynomialRingElement
          in
          re, zeta_i <: (t_PolynomialRingElement & usize))
  in
  let hax_temp_output:t_PolynomialRingElement = re in
  zeta_i, hax_temp_output <: (usize & t_PolynomialRingElement)

let ntt_layer_7_int_vec_step (a b: Libcrux_ml_kem.Simd.Portable.t_PortableVector) =
  let t:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
    Libcrux_ml_kem.Simd.Simd_trait.f_multiply_by_constant b (-1600l)
  in
  let b:Libcrux_ml_kem.Simd.Portable.t_PortableVector = Libcrux_ml_kem.Simd.Simd_trait.f_sub a t in
  let a:Libcrux_ml_kem.Simd.Portable.t_PortableVector = Libcrux_ml_kem.Simd.Simd_trait.f_add a t in
  a, b
  <:
  (Libcrux_ml_kem.Simd.Portable.t_PortableVector & Libcrux_ml_kem.Simd.Portable.t_PortableVector)

let ntt_at_layer_7_ (re: t_PolynomialRingElement) =
  let step:usize = v_VECTORS_IN_RING_ELEMENT /! sz 2 in
  let re:t_PolynomialRingElement =
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
          let re:t_PolynomialRingElement = re in
          let j:usize = j in
          let x, y:(Libcrux_ml_kem.Simd.Portable.t_PortableVector &
            Libcrux_ml_kem.Simd.Portable.t_PortableVector) =
            ntt_layer_7_int_vec_step (re.f_coefficients.[ j ]
                <:
                Libcrux_ml_kem.Simd.Portable.t_PortableVector)
              (re.f_coefficients.[ j +! step <: usize ]
                <:
                Libcrux_ml_kem.Simd.Portable.t_PortableVector)
          in
          let re:t_PolynomialRingElement =
            {
              re with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_coefficients j x
            }
            <:
            t_PolynomialRingElement
          in
          let re:t_PolynomialRingElement =
            {
              re with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_coefficients
                (j +! step <: usize)
                y
            }
            <:
            t_PolynomialRingElement
          in
          re)
  in
  re

let ntt_layer_int_vec_step (a b: Libcrux_ml_kem.Simd.Portable.t_PortableVector) (zeta_r: i32) =
  let t:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
    Libcrux_ml_kem.Simd.Simd_trait.f_montgomery_multiply_fe_by_fer b zeta_r
  in
  let b:Libcrux_ml_kem.Simd.Portable.t_PortableVector = Libcrux_ml_kem.Simd.Simd_trait.f_sub a t in
  let a:Libcrux_ml_kem.Simd.Portable.t_PortableVector = Libcrux_ml_kem.Simd.Simd_trait.f_add a t in
  a, b
  <:
  (Libcrux_ml_kem.Simd.Portable.t_PortableVector & Libcrux_ml_kem.Simd.Portable.t_PortableVector)

let ntt_at_layer_3_plus
      (zeta_i: usize)
      (re: t_PolynomialRingElement)
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
  let re, zeta_i:(t_PolynomialRingElement & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 128 >>! layer <: usize
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      (re, zeta_i <: (t_PolynomialRingElement & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(t_PolynomialRingElement & usize) = temp_0_ in
          let round:usize = round in
          let zeta_i:usize = zeta_i +! sz 1 in
          let offset:usize = (round *! step <: usize) *! sz 2 in
          let offset_vec:usize =
            offset /! Libcrux_ml_kem.Simd.Simd_trait.f_FIELD_ELEMENTS_IN_VECTOR
          in
          let step_vec:usize = step /! Libcrux_ml_kem.Simd.Simd_trait.f_FIELD_ELEMENTS_IN_VECTOR in
          let re:t_PolynomialRingElement =
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
                  let re:t_PolynomialRingElement = re in
                  let j:usize = j in
                  let x, y:(Libcrux_ml_kem.Simd.Portable.t_PortableVector &
                    Libcrux_ml_kem.Simd.Portable.t_PortableVector) =
                    ntt_layer_int_vec_step (re.f_coefficients.[ j ]
                        <:
                        Libcrux_ml_kem.Simd.Portable.t_PortableVector)
                      (re.f_coefficients.[ j +! step_vec <: usize ]
                        <:
                        Libcrux_ml_kem.Simd.Portable.t_PortableVector)
                      (v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i ] <: i32)
                  in
                  let re:t_PolynomialRingElement =
                    {
                      re with
                      f_coefficients
                      =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_coefficients
                        j
                        x
                    }
                    <:
                    t_PolynomialRingElement
                  in
                  let re:t_PolynomialRingElement =
                    {
                      re with
                      f_coefficients
                      =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_coefficients
                        (j +! step_vec <: usize)
                        y
                    }
                    <:
                    t_PolynomialRingElement
                  in
                  re)
          in
          re, zeta_i <: (t_PolynomialRingElement & usize))
  in
  let hax_temp_output:t_PolynomialRingElement = re in
  zeta_i, hax_temp_output <: (usize & t_PolynomialRingElement)

let ntt_multiply (lhs rhs: t_PolynomialRingElement) =
  let out:t_PolynomialRingElement = impl__PolynomialRingElement__ZERO () in
  let out:t_PolynomialRingElement =
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
          let out:t_PolynomialRingElement = out in
          let i:usize = i in
          {
            out with
            f_coefficients
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_coefficients
              i
              (Libcrux_ml_kem.Simd.Simd_trait.f_ntt_multiply (lhs.f_coefficients.[ i ]
                    <:
                    Libcrux_ml_kem.Simd.Portable.t_PortableVector)
                  (rhs.f_coefficients.[ i ] <: Libcrux_ml_kem.Simd.Portable.t_PortableVector)
                  (v_ZETAS_TIMES_MONTGOMERY_R.[ sz 64 +! (sz 2 *! i <: usize) <: usize ] <: i32)
                  (v_ZETAS_TIMES_MONTGOMERY_R.[ (sz 64 +! (sz 2 *! i <: usize) <: usize) +! sz 1
                      <:
                      usize ]
                    <:
                    i32)
                <:
                Libcrux_ml_kem.Simd.Portable.t_PortableVector)
            <:
            t_Array Libcrux_ml_kem.Simd.Portable.t_PortableVector (sz 32)
          }
          <:
          t_PolynomialRingElement)
  in
  out

let poly_barrett_reduce (a: t_PolynomialRingElement) =
  let a:t_PolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_VECTORS_IN_RING_ELEMENT
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      a
      (fun a i ->
          let a:t_PolynomialRingElement = a in
          let i:usize = i in
          {
            a with
            f_coefficients
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_coefficients
              i
              (Libcrux_ml_kem.Simd.Simd_trait.f_barrett_reduce (a.f_coefficients.[ i ]
                    <:
                    Libcrux_ml_kem.Simd.Portable.t_PortableVector)
                <:
                Libcrux_ml_kem.Simd.Portable.t_PortableVector)
            <:
            t_Array Libcrux_ml_kem.Simd.Portable.t_PortableVector (sz 32)
          }
          <:
          t_PolynomialRingElement)
  in
  a

let subtract_reduce (a b: t_PolynomialRingElement) =
  let b:t_PolynomialRingElement =
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
          let b:t_PolynomialRingElement = b in
          let i:usize = i in
          let coefficient_normal_form:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
            Libcrux_ml_kem.Simd.Simd_trait.f_montgomery_reduce (Libcrux_ml_kem.Simd.Simd_trait.f_multiply_by_constant
                  (b.f_coefficients.[ i ] <: Libcrux_ml_kem.Simd.Portable.t_PortableVector)
                  1441l
                <:
                Libcrux_ml_kem.Simd.Portable.t_PortableVector)
          in
          let b:t_PolynomialRingElement =
            {
              b with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize b.f_coefficients
                i
                (Libcrux_ml_kem.Simd.Simd_trait.f_barrett_reduce (Libcrux_ml_kem.Simd.Simd_trait.f_sub
                        (a.f_coefficients.[ i ] <: Libcrux_ml_kem.Simd.Portable.t_PortableVector)
                        coefficient_normal_form
                      <:
                      Libcrux_ml_kem.Simd.Portable.t_PortableVector)
                  <:
                  Libcrux_ml_kem.Simd.Portable.t_PortableVector)
            }
            <:
            t_PolynomialRingElement
          in
          b)
  in
  b
