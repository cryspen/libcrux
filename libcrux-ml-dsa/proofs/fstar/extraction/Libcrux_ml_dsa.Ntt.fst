module Libcrux_ml_dsa.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

let invert_ntt_at_layer_0_
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
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_dsa.Polynomial.f_simd_units
        (sz 0)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_0_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 0 ] <: v_SIMDUnit)
            1976782l
            (-846154l)
            1400424l
            3937738l
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
        (sz 1)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_0_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 1 ] <: v_SIMDUnit)
            (-1362209l)
            (-48306l)
            3919660l
            (-554416l)
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
        (sz 2)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_0_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 2 ] <: v_SIMDUnit)
            (-3545687l)
            1612842l
            (-976891l)
            183443l
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
        (sz 3)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_0_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 3 ] <: v_SIMDUnit)
            (-2286327l)
            (-420899l)
            (-2235985l)
            (-2939036l)
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
        (sz 4)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_0_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 4 ] <: v_SIMDUnit)
            (-3833893l)
            (-260646l)
            (-1104333l)
            (-1667432l)
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
        (sz 5)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_0_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 5 ] <: v_SIMDUnit)
            1910376l
            (-1803090l)
            1723600l
            (-426683l)
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
        (sz 6)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_0_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 6 ] <: v_SIMDUnit)
            472078l
            1717735l
            (-975884l)
            2213111l
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
        (sz 7)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_0_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 7 ] <: v_SIMDUnit)
            269760l
            3866901l
            3523897l
            (-3038916l)
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
        (sz 8)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_0_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 8 ] <: v_SIMDUnit)
            (-1799107l)
            (-3694233l)
            1652634l
            810149l
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
        (sz 9)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_0_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 9 ] <: v_SIMDUnit)
            3014001l
            1616392l
            162844l
            (-3183426l)
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
        (sz 10)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_0_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 10 ] <: v_SIMDUnit)
            (-1207385l)
            185531l
            3369112l
            1957272l
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
        (sz 11)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_0_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 11 ] <: v_SIMDUnit)
            (-164721l)
            2454455l
            2432395l
            (-2013608l)
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
        (sz 12)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_0_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 12 ] <: v_SIMDUnit)
            (-3776993l)
            594136l
            (-3724270l)
            (-2584293l)
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
        (sz 13)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_0_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 13 ] <: v_SIMDUnit)
            (-1846953l)
            (-1671176l)
            (-2831860l)
            (-542412l)
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
        (sz 14)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_0_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 14 ] <: v_SIMDUnit)
            3406031l
            2235880l
            777191l
            1500165l
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
        (sz 15)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_0_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 15 ] <: v_SIMDUnit)
            (-1374803l)
            (-2546312l)
            1917081l
            (-1279661l)
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
        (sz 16)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_0_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 16 ] <: v_SIMDUnit)
            (-1962642l)
            3306115l
            1312455l
            (-451100l)
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
        (sz 17)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_0_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 17 ] <: v_SIMDUnit)
            (-1430225l)
            (-3318210l)
            1237275l
            (-1333058l)
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
        (sz 18)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_0_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 18 ] <: v_SIMDUnit)
            (-1050970l)
            1903435l
            1869119l
            (-2994039l)
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
        (sz 19)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_0_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 19 ] <: v_SIMDUnit)
            (-3548272l)
            2635921l
            1250494l
            (-3767016l)
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
        (sz 20)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_0_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 20 ] <: v_SIMDUnit)
            1595974l
            2486353l
            1247620l
            4055324l
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
        (sz 21)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_0_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 21 ] <: v_SIMDUnit)
            1265009l
            (-2590150l)
            2691481l
            2842341l
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
        (sz 22)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_0_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 22 ] <: v_SIMDUnit)
            203044l
            1735879l
            (-3342277l)
            3437287l
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
        (sz 23)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_0_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 23 ] <: v_SIMDUnit)
            4108315l
            (-2437823l)
            286988l
            342297l
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
        (sz 24)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_0_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 24 ] <: v_SIMDUnit)
            (-3595838l)
            (-768622l)
            (-525098l)
            (-3556995l)
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
        (sz 25)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_0_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 25 ] <: v_SIMDUnit)
            3207046l
            2031748l
            (-3122442l)
            (-655327l)
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
        (sz 26)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_0_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 26 ] <: v_SIMDUnit)
            (-522500l)
            (-43260l)
            (-1613174l)
            495491l
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
        (sz 27)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_0_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 27 ] <: v_SIMDUnit)
            819034l
            909542l
            1859098l
            900702l
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
        (sz 28)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_0_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 28 ] <: v_SIMDUnit)
            (-3193378l)
            (-1197226l)
            (-3759364l)
            (-3520352l)
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
        (sz 29)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_0_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 29 ] <: v_SIMDUnit)
            3513181l
            (-1235728l)
            2434439l
            266997l
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
        (sz 30)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_0_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 30 ] <: v_SIMDUnit)
            (-3562462l)
            (-2446433l)
            2244091l
            (-3342478l)
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
        (sz 31)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_0_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 31 ] <: v_SIMDUnit)
            3817976l
            2316500l
            3407706l
            2091667l
          <:
          v_SIMDUnit)
    }
    <:
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit
  in
  re

let invert_ntt_at_layer_1_
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
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_dsa.Polynomial.f_simd_units
        (sz 0)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_1_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 0 ] <: v_SIMDUnit)
            3839961l
            (-3628969l)
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
        (sz 1)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_1_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 1 ] <: v_SIMDUnit)
            (-3881060l)
            (-3019102l)
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
        (sz 2)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_1_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 2 ] <: v_SIMDUnit)
            (-1439742l)
            (-812732l)
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
        (sz 3)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_1_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 3 ] <: v_SIMDUnit)
            (-1584928l)
            1285669l
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
        (sz 4)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_1_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 4 ] <: v_SIMDUnit)
            1341330l
            1315589l
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
        (sz 5)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_1_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 5 ] <: v_SIMDUnit)
            (-177440l)
            (-2409325l)
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
        (sz 6)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_1_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 6 ] <: v_SIMDUnit)
            (-1851402l)
            3159746l
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
        (sz 7)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_1_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 7 ] <: v_SIMDUnit)
            (-3553272l)
            189548l
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
        (sz 8)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_1_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 8 ] <: v_SIMDUnit)
            (-1316856l)
            759969l
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
        (sz 9)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_1_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 9 ] <: v_SIMDUnit)
            (-210977l)
            2389356l
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
        (sz 10)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_1_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 10 ] <: v_SIMDUnit)
            (-3249728l)
            1653064l
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
        (sz 11)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_1_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 11 ] <: v_SIMDUnit)
            (-8578l)
            (-3724342l)
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
        (sz 12)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_1_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 12 ] <: v_SIMDUnit)
            3958618l
            904516l
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
        (sz 13)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_1_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 13 ] <: v_SIMDUnit)
            (-1100098l)
            44288l
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
        (sz 14)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_1_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 14 ] <: v_SIMDUnit)
            3097992l
            508951l
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
        (sz 15)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_1_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 15 ] <: v_SIMDUnit)
            264944l
            (-3343383l)
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
        (sz 16)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_1_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 16 ] <: v_SIMDUnit)
            (-1430430l)
            1852771l
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
        (sz 17)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_1_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 17 ] <: v_SIMDUnit)
            1349076l
            (-381987l)
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
        (sz 18)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_1_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 18 ] <: v_SIMDUnit)
            (-1308169l)
            (-22981l)
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
        (sz 19)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_1_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 19 ] <: v_SIMDUnit)
            (-1228525l)
            (-671102l)
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
        (sz 20)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_1_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 20 ] <: v_SIMDUnit)
            (-2477047l)
            (-411027l)
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
        (sz 21)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_1_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 21 ] <: v_SIMDUnit)
            (-3693493l)
            (-2967645l)
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
        (sz 22)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_1_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 22 ] <: v_SIMDUnit)
            2715295l
            2147896l
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
        (sz 23)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_1_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 23 ] <: v_SIMDUnit)
            (-983419l)
            3412210l
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
        (sz 24)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_1_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 24 ] <: v_SIMDUnit)
            126922l
            (-3632928l)
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
        (sz 25)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_1_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 25 ] <: v_SIMDUnit)
            (-3157330l)
            (-3190144l)
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
        (sz 26)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_1_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 26 ] <: v_SIMDUnit)
            (-1000202l)
            (-4083598l)
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
        (sz 27)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_1_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 27 ] <: v_SIMDUnit)
            1939314l
            (-1257611l)
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
        (sz 28)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_1_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 28 ] <: v_SIMDUnit)
            (-1585221l)
            2176455l
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
        (sz 29)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_1_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 29 ] <: v_SIMDUnit)
            3475950l
            (-1452451l)
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
        (sz 30)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_1_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 30 ] <: v_SIMDUnit)
            (-3041255l)
            (-3677745l)
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
        (sz 31)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_1_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 31 ] <: v_SIMDUnit)
            (-1528703l)
            (-3930395l)
          <:
          v_SIMDUnit)
    }
    <:
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit
  in
  re

let invert_ntt_at_layer_2_
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
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_dsa.Polynomial.f_simd_units
        (sz 0)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_2_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 0 ] <: v_SIMDUnit)
            (-2797779l)
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
        (sz 1)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_2_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 1 ] <: v_SIMDUnit)
            2071892l
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
        (sz 2)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_2_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 2 ] <: v_SIMDUnit)
            (-2556880l)
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
        (sz 3)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_2_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 3 ] <: v_SIMDUnit)
            3900724l
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
        (sz 4)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_2_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 4 ] <: v_SIMDUnit)
            3881043l
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
        (sz 5)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_2_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 5 ] <: v_SIMDUnit)
            954230l
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
        (sz 6)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_2_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 6 ] <: v_SIMDUnit)
            531354l
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
        (sz 7)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_2_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 7 ] <: v_SIMDUnit)
            811944l
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
        (sz 8)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_2_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 8 ] <: v_SIMDUnit)
            3699596l
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
        (sz 9)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_2_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 9 ] <: v_SIMDUnit)
            (-1600420l)
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
        (sz 10)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_2_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 10 ] <: v_SIMDUnit)
            (-2140649l)
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
        (sz 11)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_2_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 11 ] <: v_SIMDUnit)
            3507263l
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
        (sz 12)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_2_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 12 ] <: v_SIMDUnit)
            (-3821735l)
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
        (sz 13)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_2_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 13 ] <: v_SIMDUnit)
            3505694l
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
        (sz 14)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_2_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 14 ] <: v_SIMDUnit)
            (-1643818l)
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
        (sz 15)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_2_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 15 ] <: v_SIMDUnit)
            (-1699267l)
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
        (sz 16)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_2_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 16 ] <: v_SIMDUnit)
            (-539299l)
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
        (sz 17)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_2_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 17 ] <: v_SIMDUnit)
            2348700l
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
        (sz 18)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_2_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 18 ] <: v_SIMDUnit)
            (-300467l)
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
        (sz 19)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_2_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 19 ] <: v_SIMDUnit)
            3539968l
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
        (sz 20)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_2_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 20 ] <: v_SIMDUnit)
            (-2867647l)
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
        (sz 21)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_2_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 21 ] <: v_SIMDUnit)
            3574422l
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
        (sz 22)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_2_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 22 ] <: v_SIMDUnit)
            (-3043716l)
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
        (sz 23)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_2_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 23 ] <: v_SIMDUnit)
            (-3861115l)
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
        (sz 24)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_2_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 24 ] <: v_SIMDUnit)
            3915439l
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
        (sz 25)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_2_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 25 ] <: v_SIMDUnit)
            (-2537516l)
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
        (sz 26)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_2_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 26 ] <: v_SIMDUnit)
            (-3592148l)
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
        (sz 27)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_2_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 27 ] <: v_SIMDUnit)
            (-1661693l)
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
        (sz 28)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_2_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 28 ] <: v_SIMDUnit)
            3530437l
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
        (sz 29)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_2_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 29 ] <: v_SIMDUnit)
            3077325l
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
        (sz 30)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_2_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 30 ] <: v_SIMDUnit)
            95776l
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
        (sz 31)
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_2_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ sz 31 ] <: v_SIMDUnit)
            2706023l
          <:
          v_SIMDUnit)
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
  {
    Libcrux_ml_dsa.Polynomial.f_simd_units
    =
    Libcrux_ml_dsa.Simd.Traits.f_ntt #v_SIMDUnit
      #FStar.Tactics.Typeclasses.solve
      re.Libcrux_ml_dsa.Polynomial.f_simd_units
  }
  <:
  Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit

let outer_3_plus
      (#v_SIMDUnit: Type0)
      (v_OFFSET v_STEP_BY: usize)
      (v_ZETA: i32)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
     =
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    Rust_primitives.Hax.Folds.fold_range v_OFFSET
      (v_OFFSET +! v_STEP_BY <: usize)
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
              (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ j +! v_STEP_BY <: usize ] <: v_SIMDUnit)
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
                    (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ j +! v_STEP_BY <: usize ]
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
                (j +! v_STEP_BY <: usize)
                (Libcrux_ml_dsa.Simd.Traits.montgomery_multiply_by_fer #v_SIMDUnit a_minus_b v_ZETA
                  <:
                  v_SIMDUnit)
            }
            <:
            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit
          in
          re)
  in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  re

let invert_ntt_at_layer_3_
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
     =
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    outer_3_plus #v_SIMDUnit (sz 0) (sz 1) 280005l re
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    outer_3_plus #v_SIMDUnit (sz 2) (sz 1) 4010497l re
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    outer_3_plus #v_SIMDUnit (sz 4) (sz 1) (-19422l) re
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    outer_3_plus #v_SIMDUnit (sz 6) (sz 1) 1757237l re
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    outer_3_plus #v_SIMDUnit (sz 8) (sz 1) (-3277672l) re
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    outer_3_plus #v_SIMDUnit (sz 10) (sz 1) (-1399561l) re
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    outer_3_plus #v_SIMDUnit (sz 12) (sz 1) (-3859737l) re
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    outer_3_plus #v_SIMDUnit (sz 14) (sz 1) (-2118186l) re
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    outer_3_plus #v_SIMDUnit (sz 16) (sz 1) (-2108549l) re
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    outer_3_plus #v_SIMDUnit (sz 18) (sz 1) 2619752l re
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    outer_3_plus #v_SIMDUnit (sz 20) (sz 1) (-1119584l) re
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    outer_3_plus #v_SIMDUnit (sz 22) (sz 1) (-549488l) re
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    outer_3_plus #v_SIMDUnit (sz 24) (sz 1) 3585928l re
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    outer_3_plus #v_SIMDUnit (sz 26) (sz 1) (-1079900l) re
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    outer_3_plus #v_SIMDUnit (sz 28) (sz 1) 1024112l re
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    outer_3_plus #v_SIMDUnit (sz 30) (sz 1) 2725464l re
  in
  re

let invert_ntt_at_layer_4_
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
     =
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    outer_3_plus #v_SIMDUnit (sz 0) (sz 2) 2680103l re
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    outer_3_plus #v_SIMDUnit (sz 4) (sz 2) 3111497l re
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    outer_3_plus #v_SIMDUnit (sz 8) (sz 2) (-2884855l) re
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    outer_3_plus #v_SIMDUnit (sz 12) (sz 2) 3119733l re
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    outer_3_plus #v_SIMDUnit (sz 16) (sz 2) (-2091905l) re
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    outer_3_plus #v_SIMDUnit (sz 20) (sz 2) (-359251l) re
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    outer_3_plus #v_SIMDUnit (sz 24) (sz 2) 2353451l re
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    outer_3_plus #v_SIMDUnit (sz 28) (sz 2) 1826347l re
  in
  re

let invert_ntt_at_layer_5_
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
     =
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    outer_3_plus #v_SIMDUnit (sz 0) (sz 4) 466468l re
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    outer_3_plus #v_SIMDUnit (sz 8) (sz 4) (-876248l) re
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    outer_3_plus #v_SIMDUnit (sz 16) (sz 4) (-777960l) re
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    outer_3_plus #v_SIMDUnit (sz 24) (sz 4) 237124l re
  in
  re

let invert_ntt_at_layer_6_
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
     =
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    outer_3_plus #v_SIMDUnit (sz 0) (sz 8) (-518909l) re
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    outer_3_plus #v_SIMDUnit (sz 16) (sz 8) (-2608894l) re
  in
  re

let invert_ntt_at_layer_7_
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
     =
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    outer_3_plus #v_SIMDUnit (sz 0) (sz 16) 25847l re
  in
  re

let invert_ntt_montgomery
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
     =
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_0_ #v_SIMDUnit re
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_1_ #v_SIMDUnit re
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_2_ #v_SIMDUnit re
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_3_ #v_SIMDUnit re
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_4_ #v_SIMDUnit re
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_5_ #v_SIMDUnit re
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_6_ #v_SIMDUnit re
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_7_ #v_SIMDUnit re
  in
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
