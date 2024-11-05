module Libcrux_ml_dsa.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

let ntt
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
     =
  {
    Libcrux_ml_dsa.Polynomial.f_simd_units
    =
    Libcrux_ml_dsa.Simd.Traits.f_ntt #v_SIMDUnit
      #FStar.Tactics.Typeclasses.solve
      re.Libcrux_ml_dsa.Polynomial.f_simd_units
  }
  <:
  Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit

let invert_ntt_at_layer_1_
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (zeta_i: usize)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
     =
  let zeta_i:usize = zeta_i -! sz 1 in
  let re, zeta_i:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit & usize) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (sz 256 /! Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT <: usize)
      (fun temp_0_ temp_1_ ->
          let re, zeta_i:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit & usize) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (re, zeta_i <: (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit & usize) =
            temp_0_
          in
          let round:usize = round in
          let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
            {
              re with
              Libcrux_ml_dsa.Polynomial.f_simd_units
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_ml_dsa.Polynomial.f_simd_units
                round
                (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_1_ #v_SIMDUnit
                    #FStar.Tactics.Typeclasses.solve
                    (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ round ] <: v_SIMDUnit)
                    (v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i ] <: i32)
                    (v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i -! sz 1 <: usize ] <: i32)
                  <:
                  v_SIMDUnit)
            }
            <:
            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit
          in
          let zeta_i:usize = zeta_i -! sz 2 in
          re, zeta_i <: (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit & usize))
  in
  let zeta_i:usize = zeta_i +! sz 1 in
  zeta_i, re <: (usize & Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)

let invert_ntt_at_layer_2_
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (zeta_i: usize)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
     =
  let re, zeta_i:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit & usize) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (sz 256 /! Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT <: usize)
      (fun temp_0_ temp_1_ ->
          let re, zeta_i:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit & usize) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (re, zeta_i <: (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit & usize) =
            temp_0_
          in
          let round:usize = round in
          let zeta_i:usize = zeta_i -! sz 1 in
          let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
            {
              re with
              Libcrux_ml_dsa.Polynomial.f_simd_units
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_ml_dsa.Polynomial.f_simd_units
                round
                (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_2_ #v_SIMDUnit
                    #FStar.Tactics.Typeclasses.solve
                    (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ round ] <: v_SIMDUnit)
                    (v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i ] <: i32)
                  <:
                  v_SIMDUnit)
            }
            <:
            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit
          in
          re, zeta_i <: (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit & usize))
  in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  zeta_i, re <: (usize & Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)

let invert_ntt_at_layer_3_plus
      (#v_SIMDUnit: Type0)
      (v_LAYER: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (zeta_i: usize)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
     =
  let step:usize = sz 1 <<! v_LAYER in
  let re, zeta_i:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit & usize) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (sz 128 >>! v_LAYER <: usize)
      (fun temp_0_ temp_1_ ->
          let re, zeta_i:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit & usize) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (re, zeta_i <: (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit & usize) =
            temp_0_
          in
          let round:usize = round in
          let zeta_i:usize = zeta_i -! sz 1 in
          let offset:usize =
            ((round *! step <: usize) *! sz 2 <: usize) /!
            Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT
          in
          let step_by:usize = step /! Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT in
          let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
            Rust_primitives.Hax.Folds.fold_range offset
              (offset +! step_by <: usize)
              (fun re temp_1_ ->
                  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit = re in
                  let _:usize = temp_1_ in
                  true)
              re
              (fun re j ->
                  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit = re in
                  let j:usize = j in
                  let a_minus_b:v_SIMDUnit =
                    Libcrux_ml_dsa.Simd.Traits.f_subtract #v_SIMDUnit
                      #FStar.Tactics.Typeclasses.solve
                      (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ j +! step_by <: usize ]
                        <:
                        v_SIMDUnit)
                      (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ j ] <: v_SIMDUnit)
                  in
                  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
                    {
                      re with
                      Libcrux_ml_dsa.Polynomial.f_simd_units
                      =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                          .Libcrux_ml_dsa.Polynomial.f_simd_units
                        j
                        (Libcrux_ml_dsa.Simd.Traits.f_add #v_SIMDUnit
                            #FStar.Tactics.Typeclasses.solve
                            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ j ] <: v_SIMDUnit)
                            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ j +! step_by <: usize ]
                              <:
                              v_SIMDUnit)
                          <:
                          v_SIMDUnit)
                    }
                    <:
                    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit
                  in
                  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
                    {
                      re with
                      Libcrux_ml_dsa.Polynomial.f_simd_units
                      =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                          .Libcrux_ml_dsa.Polynomial.f_simd_units
                        (j +! step_by <: usize)
                        (Libcrux_ml_dsa.Simd.Traits.montgomery_multiply_by_fer #v_SIMDUnit
                            a_minus_b
                            (v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i ] <: i32)
                          <:
                          v_SIMDUnit)
                    }
                    <:
                    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit
                  in
                  re)
          in
          re, zeta_i <: (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit & usize))
  in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  zeta_i, re <: (usize & Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)

let invert_ntt_at_layer_0_
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (zeta_i: usize)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
     =
  let zeta_i:usize = zeta_i -! sz 1 in
  let re, zeta_i:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit & usize) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #v_SIMDUnit
          (re.Libcrux_ml_dsa.Polynomial.f_simd_units <: t_Slice v_SIMDUnit)
        <:
        usize)
      (fun temp_0_ temp_1_ ->
          let re, zeta_i:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit & usize) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (re, zeta_i <: (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit & usize) =
            temp_0_
          in
          let round:usize = round in
          let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
            {
              re with
              Libcrux_ml_dsa.Polynomial.f_simd_units
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_ml_dsa.Polynomial.f_simd_units
                round
                (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_0_ #v_SIMDUnit
                    #FStar.Tactics.Typeclasses.solve
                    (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ round ] <: v_SIMDUnit)
                    (v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i ] <: i32)
                    (v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i -! sz 1 <: usize ] <: i32)
                    (v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i -! sz 2 <: usize ] <: i32)
                    (v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i -! sz 3 <: usize ] <: i32)
                  <:
                  v_SIMDUnit)
            }
            <:
            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit
          in
          let zeta_i:usize = zeta_i -! sz 4 in
          re, zeta_i <: (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit & usize))
  in
  let zeta_i:usize = zeta_i +! sz 1 in
  zeta_i, re <: (usize & Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)

let invert_ntt_montgomery
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
     =
  let zeta_i:usize = Libcrux_ml_dsa.Constants.v_COEFFICIENTS_IN_RING_ELEMENT in
  let tmp0, tmp1:(usize & Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    invert_ntt_at_layer_0_ #v_SIMDUnit zeta_i re
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    invert_ntt_at_layer_1_ #v_SIMDUnit zeta_i re
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    invert_ntt_at_layer_2_ #v_SIMDUnit zeta_i re
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    invert_ntt_at_layer_3_plus #v_SIMDUnit (sz 3) zeta_i re
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    invert_ntt_at_layer_3_plus #v_SIMDUnit (sz 4) zeta_i re
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    invert_ntt_at_layer_3_plus #v_SIMDUnit (sz 5) zeta_i re
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    invert_ntt_at_layer_3_plus #v_SIMDUnit (sz 6) zeta_i re
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    invert_ntt_at_layer_3_plus #v_SIMDUnit (sz 7) zeta_i re
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit = tmp1 in
  let _:Prims.unit = () in
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
              (Libcrux_ml_dsa.Simd.Traits.f_montgomery_multiply_by_constant #v_SIMDUnit
                  #FStar.Tactics.Typeclasses.solve
                  (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ i ] <: v_SIMDUnit)
                  41978l
                <:
                v_SIMDUnit)
            <:
            t_Array v_SIMDUnit (sz 32)
          }
          <:
          Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
  in
  re

let ntt_multiply_montgomery
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (lhs rhs: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
     =
  let out:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    Libcrux_ml_dsa.Polynomial.impl__ZERO #v_SIMDUnit ()
  in
  let out:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #v_SIMDUnit
          (out.Libcrux_ml_dsa.Polynomial.f_simd_units <: t_Slice v_SIMDUnit)
        <:
        usize)
      (fun out temp_1_ ->
          let out:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit = out in
          let _:usize = temp_1_ in
          true)
      out
      (fun out i ->
          let out:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit = out in
          let i:usize = i in
          {
            out with
            Libcrux_ml_dsa.Polynomial.f_simd_units
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
                .Libcrux_ml_dsa.Polynomial.f_simd_units
              i
              (Libcrux_ml_dsa.Simd.Traits.f_montgomery_multiply #v_SIMDUnit
                  #FStar.Tactics.Typeclasses.solve
                  (lhs.Libcrux_ml_dsa.Polynomial.f_simd_units.[ i ] <: v_SIMDUnit)
                  (rhs.Libcrux_ml_dsa.Polynomial.f_simd_units.[ i ] <: v_SIMDUnit)
                <:
                v_SIMDUnit)
            <:
            t_Array v_SIMDUnit (sz 32)
          }
          <:
          Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
  in
  out
