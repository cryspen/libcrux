module Libcrux_ml_dsa.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

let invert_ntt_montgomery
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
     =
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    {
      re with
      Libcrux_ml_dsa.Polynomial.f_simd_units
      =
      Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_montgomery #v_SIMDUnit
        #FStar.Tactics.Typeclasses.solve
        re.Libcrux_ml_dsa.Polynomial.f_simd_units
    }
    <:
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit
  in
  re

let ntt
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
     =
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    {
      re with
      Libcrux_ml_dsa.Polynomial.f_simd_units
      =
      Libcrux_ml_dsa.Simd.Traits.f_ntt #v_SIMDUnit
        #FStar.Tactics.Typeclasses.solve
        re.Libcrux_ml_dsa.Polynomial.f_simd_units
    }
    <:
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit
  in
  re

let ntt_multiply_montgomery
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (lhs rhs: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
     =
  let lhs:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (Core.Slice.impl__len #v_SIMDUnit
          (lhs.Libcrux_ml_dsa.Polynomial.f_simd_units <: t_Slice v_SIMDUnit)
        <:
        usize)
      (fun lhs temp_1_ ->
          let lhs:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit = lhs in
          let _:usize = temp_1_ in
          true)
      lhs
      (fun lhs i ->
          let lhs:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit = lhs in
          let i:usize = i in
          {
            lhs with
            Libcrux_ml_dsa.Polynomial.f_simd_units
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize lhs
                .Libcrux_ml_dsa.Polynomial.f_simd_units
              i
              (Libcrux_ml_dsa.Simd.Traits.f_montgomery_multiply #v_SIMDUnit
                  #FStar.Tactics.Typeclasses.solve
                  (lhs.Libcrux_ml_dsa.Polynomial.f_simd_units.[ i ] <: v_SIMDUnit)
                  (rhs.Libcrux_ml_dsa.Polynomial.f_simd_units.[ i ] <: v_SIMDUnit)
                <:
                v_SIMDUnit)
            <:
            t_Array v_SIMDUnit (mk_usize 32)
          }
          <:
          Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
  in
  lhs
