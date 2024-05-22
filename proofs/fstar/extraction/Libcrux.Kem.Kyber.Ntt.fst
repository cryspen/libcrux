module Libcrux.Kem.Kyber.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let ntt_multiply_binomials (a0, a1: (i32 & i32)) (b0, b1: (i32 & i32)) (zeta: i32) =
  Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce ((a0 *! b0 <: i32) +!
      ((Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce (a1 *! b1 <: i32) <: i32) *! zeta <: i32)
      <:
      i32),
  Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce ((a0 *! b1 <: i32) +! (a1 *! b0 <: i32) <: i32)
  <:
  (i32 & i32)

let invert_ntt_at_layer
      (zeta_i: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
      (layer: usize)
     =
  let step:usize = sz 1 <<! layer in
  let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 128 >>! layer <: usize }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      (re, zeta_i <: (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement & usize) = temp_0_ in
          let round:usize = round in
          let zeta_i:usize = zeta_i -! sz 1 in
          let offset:usize = (round *! step <: usize) *! sz 2 in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
                    usize)
                  ({
                      Core.Ops.Range.f_start = offset;
                      Core.Ops.Range.f_end = offset +! step <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize)
                <:
                Core.Ops.Range.t_Range usize)
              re
              (fun re j ->
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = re in
                  let j:usize = j in
                  let a_minus_b:i32 =
                    (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j +! step <: usize ] <: i32) -!
                    (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                          .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        j
                        ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) +!
                          (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j +! step <: usize ]
                            <:
                            i32)
                          <:
                          i32)
                    }
                    <:
                    Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                          .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        (j +! step <: usize)
                        (Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce (a_minus_b *!
                              (v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i ] <: i32)
                              <:
                              i32)
                          <:
                          i32)
                    }
                    <:
                    Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
                  in
                  re)
          in
          re, zeta_i <: (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement & usize))
  in
  let hax_temp_output:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = re in
  zeta_i, hax_temp_output <: (usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)

let invert_ntt_montgomery (v_K: usize) (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement) =
  let _:Prims.unit = () <: Prims.unit in
  let zeta_i:usize = Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT /! sz 2 in
  let tmp0, out:(usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement) =
    invert_ntt_at_layer zeta_i re (sz 1)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = out in
  let tmp0, out:(usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement) =
    invert_ntt_at_layer zeta_i re (sz 2)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = out in
  let tmp0, out:(usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement) =
    invert_ntt_at_layer zeta_i re (sz 3)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = out in
  let tmp0, out:(usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement) =
    invert_ntt_at_layer zeta_i re (sz 4)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = out in
  let tmp0, out:(usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement) =
    invert_ntt_at_layer zeta_i re (sz 5)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = out in
  let tmp0, out:(usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement) =
    invert_ntt_at_layer zeta_i re (sz 6)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = out in
  let tmp0, out:(usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement) =
    invert_ntt_at_layer zeta_i re (sz 7)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = out in
  let _:Prims.unit = () <: Prims.unit in
  let _:Prims.unit = () <: Prims.unit in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 2 }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      re
      (fun re i ->
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = re in
          let i:usize = i in
          {
            re with
            Libcrux.Kem.Kyber.Arithmetic.f_coefficients
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              i
              (Libcrux.Kem.Kyber.Arithmetic.barrett_reduce (re
                      .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ]
                    <:
                    i32)
                <:
                i32)
            <:
            t_Array i32 (sz 256)
          }
          <:
          Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
  in
  re

let ntt_at_layer
      (zeta_i: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
      (layer v__initial_coefficient_bound: usize)
     =
  let step:usize = sz 1 <<! layer in
  let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 128 >>! layer <: usize }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      (re, zeta_i <: (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement & usize) = temp_0_ in
          let round:usize = round in
          let zeta_i:usize = zeta_i +! sz 1 in
          let offset:usize = (round *! step <: usize) *! sz 2 in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
                    usize)
                  ({
                      Core.Ops.Range.f_start = offset;
                      Core.Ops.Range.f_end = offset +! step <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize)
                <:
                Core.Ops.Range.t_Range usize)
              re
              (fun re j ->
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = re in
                  let j:usize = j in
                  let t:i32 =
                    Libcrux.Kem.Kyber.Arithmetic.montgomery_multiply_fe_by_fer (re
                          .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j +! step <: usize ]
                        <:
                        i32)
                      (v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i ] <: i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                          .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        (j +! step <: usize)
                        ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) -! t <: i32)
                    }
                    <:
                    Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                          .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        j
                        ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) +! t <: i32)
                    }
                    <:
                    Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
                  in
                  re)
          in
          re, zeta_i <: (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement & usize))
  in
  let _:Prims.unit = () <: Prims.unit in
  let hax_temp_output:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = re in
  zeta_i, hax_temp_output <: (usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)

let ntt_at_layer_3_
      (zeta_i: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
      (layer: usize)
     =
  let tmp0, out:(usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement) =
    ntt_at_layer zeta_i re layer (sz 3)
  in
  let zeta_i:usize = tmp0 in
  let hax_temp_output:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = out in
  zeta_i, hax_temp_output <: (usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)

let ntt_at_layer_3328_
      (zeta_i: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
      (layer: usize)
     =
  let tmp0, out:(usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement) =
    ntt_at_layer zeta_i re layer (sz 3328)
  in
  let zeta_i:usize = tmp0 in
  let hax_temp_output:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = out in
  zeta_i, hax_temp_output <: (usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)

let ntt_binomially_sampled_ring_element (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement) =
  let _:Prims.unit = () <: Prims.unit in
  let zeta_i:usize = sz 1 in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 128 }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      re
      (fun re j ->
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = re in
          let j:usize = j in
          let t:i32 =
            (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j +! sz 128 <: usize ] <: i32) *!
            (-1600l)
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                (j +! sz 128 <: usize)
                ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) -! t <: i32)
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                j
                ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) +! t <: i32)
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          re)
  in
  let _:Prims.unit = () <: Prims.unit in
  let tmp0, out:(usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement) =
    ntt_at_layer_3_ zeta_i re (sz 6)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = out in
  let tmp0, out:(usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement) =
    ntt_at_layer_3_ zeta_i re (sz 5)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = out in
  let tmp0, out:(usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement) =
    ntt_at_layer_3_ zeta_i re (sz 4)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = out in
  let tmp0, out:(usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement) =
    ntt_at_layer_3_ zeta_i re (sz 3)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = out in
  let tmp0, out:(usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement) =
    ntt_at_layer_3_ zeta_i re (sz 2)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = out in
  let tmp0, out:(usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement) =
    ntt_at_layer_3_ zeta_i re (sz 1)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = out in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      re
      (fun re i ->
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = re in
          let i:usize = i in
          {
            re with
            Libcrux.Kem.Kyber.Arithmetic.f_coefficients
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              i
              (Libcrux.Kem.Kyber.Arithmetic.barrett_reduce (re
                      .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ]
                    <:
                    i32)
                <:
                i32)
            <:
            t_Array i32 (sz 256)
          }
          <:
          Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
  in
  re

let ntt_multiply (lhs rhs: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement) =
  let _:Prims.unit = () <: Prims.unit in
  let out:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO
  in
  let out:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end
              =
              Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT /! sz 4 <: usize
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      out
      (fun out i ->
          let out:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = out in
          let i:usize = i in
          let product:(i32 & i32) =
            ntt_multiply_binomials ((lhs.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ sz 4 *! i
                    <:
                    usize ]
                  <:
                  i32),
                (lhs.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ (sz 4 *! i <: usize) +! sz 1
                    <:
                    usize ]
                  <:
                  i32)
                <:
                (i32 & i32))
              ((rhs.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ sz 4 *! i <: usize ] <: i32),
                (rhs.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ (sz 4 *! i <: usize) +! sz 1
                    <:
                    usize ]
                  <:
                  i32)
                <:
                (i32 & i32))
              (v_ZETAS_TIMES_MONTGOMERY_R.[ sz 64 +! i <: usize ] <: i32)
          in
          let out:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            {
              out with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                (sz 4 *! i <: usize)
                product._1
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let out:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            {
              out with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 4 *! i <: usize) +! sz 1 <: usize)
                product._2
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let product:(i32 & i32) =
            ntt_multiply_binomials ((lhs.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ (sz 4 *! i
                      <:
                      usize) +!
                    sz 2
                    <:
                    usize ]
                  <:
                  i32),
                (lhs.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ (sz 4 *! i <: usize) +! sz 3
                    <:
                    usize ]
                  <:
                  i32)
                <:
                (i32 & i32))
              ((rhs.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ (sz 4 *! i <: usize) +! sz 2
                    <:
                    usize ]
                  <:
                  i32),
                (rhs.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ (sz 4 *! i <: usize) +! sz 3
                    <:
                    usize ]
                  <:
                  i32)
                <:
                (i32 & i32))
              (Core.Ops.Arith.Neg.neg (v_ZETAS_TIMES_MONTGOMERY_R.[ sz 64 +! i <: usize ] <: i32)
                <:
                i32)
          in
          let out:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            {
              out with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 4 *! i <: usize) +! sz 2 <: usize)
                product._1
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let out:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            {
              out with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 4 *! i <: usize) +! sz 3 <: usize)
                product._2
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          out)
  in
  out

let ntt_vector_u
      (v_VECTOR_U_COMPRESSION_FACTOR: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
     =
  let _:Prims.unit = () <: Prims.unit in
  let zeta_i:usize = sz 0 in
  let tmp0, out:(usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement) =
    ntt_at_layer_3328_ zeta_i re (sz 7)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = out in
  let tmp0, out:(usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement) =
    ntt_at_layer_3328_ zeta_i re (sz 6)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = out in
  let tmp0, out:(usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement) =
    ntt_at_layer_3328_ zeta_i re (sz 5)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = out in
  let tmp0, out:(usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement) =
    ntt_at_layer_3328_ zeta_i re (sz 4)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = out in
  let tmp0, out:(usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement) =
    ntt_at_layer_3328_ zeta_i re (sz 3)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = out in
  let tmp0, out:(usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement) =
    ntt_at_layer_3328_ zeta_i re (sz 2)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = out in
  let tmp0, out:(usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement) =
    ntt_at_layer_3328_ zeta_i re (sz 1)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = out in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      re
      (fun re i ->
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = re in
          let i:usize = i in
          {
            re with
            Libcrux.Kem.Kyber.Arithmetic.f_coefficients
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              i
              (Libcrux.Kem.Kyber.Arithmetic.barrett_reduce (re
                      .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ]
                    <:
                    i32)
                <:
                i32)
            <:
            t_Array i32 (sz 256)
          }
          <:
          Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
  in
  re
