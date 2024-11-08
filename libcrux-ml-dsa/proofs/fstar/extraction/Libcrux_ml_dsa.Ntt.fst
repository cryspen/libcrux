module Libcrux_ml_dsa.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

let invert_ntt_at_layer_0___round
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      (index: usize)
      (zeta_0_ zeta_1_ zeta_2_ zeta_3_: i32)
     =
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    {
      re with
      Libcrux_ml_dsa.Polynomial.f_simd_units
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_dsa.Polynomial.f_simd_units
        index
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_0_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ index ] <: v_SIMDUnit)
            zeta_0_
            zeta_1_
            zeta_2_
            zeta_3_
          <:
          v_SIMDUnit)
    }
    <:
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit
  in
  re

let invert_ntt_at_layer_0_
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
     =
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_0___round #v_SIMDUnit re (sz 0) 1976782l (-846154l) 1400424l 3937738l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_0___round #v_SIMDUnit re (sz 1) (-1362209l) (-48306l) 3919660l (-554416l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_0___round #v_SIMDUnit re (sz 2) (-3545687l) 1612842l (-976891l) 183443l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_0___round #v_SIMDUnit
      re
      (sz 3)
      (-2286327l)
      (-420899l)
      (-2235985l)
      (-2939036l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_0___round #v_SIMDUnit
      re
      (sz 4)
      (-3833893l)
      (-260646l)
      (-1104333l)
      (-1667432l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_0___round #v_SIMDUnit re (sz 5) 1910376l (-1803090l) 1723600l (-426683l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_0___round #v_SIMDUnit re (sz 6) 472078l 1717735l (-975884l) 2213111l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_0___round #v_SIMDUnit re (sz 7) 269760l 3866901l 3523897l (-3038916l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_0___round #v_SIMDUnit re (sz 8) (-1799107l) (-3694233l) 1652634l 810149l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_0___round #v_SIMDUnit re (sz 9) 3014001l 1616392l 162844l (-3183426l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_0___round #v_SIMDUnit re (sz 10) (-1207385l) 185531l 3369112l 1957272l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_0___round #v_SIMDUnit re (sz 11) (-164721l) 2454455l 2432395l (-2013608l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_0___round #v_SIMDUnit re (sz 12) (-3776993l) 594136l (-3724270l) (-2584293l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_0___round #v_SIMDUnit
      re
      (sz 13)
      (-1846953l)
      (-1671176l)
      (-2831860l)
      (-542412l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_0___round #v_SIMDUnit re (sz 14) 3406031l 2235880l 777191l 1500165l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_0___round #v_SIMDUnit
      re
      (sz 15)
      (-1374803l)
      (-2546312l)
      1917081l
      (-1279661l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_0___round #v_SIMDUnit re (sz 16) (-1962642l) 3306115l 1312455l (-451100l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_0___round #v_SIMDUnit
      re
      (sz 17)
      (-1430225l)
      (-3318210l)
      1237275l
      (-1333058l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_0___round #v_SIMDUnit re (sz 18) (-1050970l) 1903435l 1869119l (-2994039l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_0___round #v_SIMDUnit re (sz 19) (-3548272l) 2635921l 1250494l (-3767016l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_0___round #v_SIMDUnit re (sz 20) 1595974l 2486353l 1247620l 4055324l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_0___round #v_SIMDUnit re (sz 21) 1265009l (-2590150l) 2691481l 2842341l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_0___round #v_SIMDUnit re (sz 22) 203044l 1735879l (-3342277l) 3437287l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_0___round #v_SIMDUnit re (sz 23) 4108315l (-2437823l) 286988l 342297l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_0___round #v_SIMDUnit
      re
      (sz 24)
      (-3595838l)
      (-768622l)
      (-525098l)
      (-3556995l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_0___round #v_SIMDUnit re (sz 25) 3207046l 2031748l (-3122442l) (-655327l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_0___round #v_SIMDUnit re (sz 26) (-522500l) (-43260l) (-1613174l) 495491l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_0___round #v_SIMDUnit re (sz 27) 819034l 909542l 1859098l 900702l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_0___round #v_SIMDUnit
      re
      (sz 28)
      (-3193378l)
      (-1197226l)
      (-3759364l)
      (-3520352l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_0___round #v_SIMDUnit re (sz 29) 3513181l (-1235728l) 2434439l 266997l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_0___round #v_SIMDUnit
      re
      (sz 30)
      (-3562462l)
      (-2446433l)
      2244091l
      (-3342478l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_0___round #v_SIMDUnit re (sz 31) 3817976l 2316500l 3407706l 2091667l
  in
  re

let invert_ntt_at_layer_1___round
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      (index: usize)
      (zeta_0_ zeta_1_: i32)
     =
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    {
      re with
      Libcrux_ml_dsa.Polynomial.f_simd_units
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_dsa.Polynomial.f_simd_units
        index
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_1_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ index ] <: v_SIMDUnit)
            zeta_0_
            zeta_1_
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
    invert_ntt_at_layer_1___round #v_SIMDUnit re (sz 0) 3839961l (-3628969l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_1___round #v_SIMDUnit re (sz 1) (-3881060l) (-3019102l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_1___round #v_SIMDUnit re (sz 2) (-1439742l) (-812732l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_1___round #v_SIMDUnit re (sz 3) (-1584928l) 1285669l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_1___round #v_SIMDUnit re (sz 4) 1341330l 1315589l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_1___round #v_SIMDUnit re (sz 5) (-177440l) (-2409325l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_1___round #v_SIMDUnit re (sz 6) (-1851402l) 3159746l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_1___round #v_SIMDUnit re (sz 7) (-3553272l) 189548l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_1___round #v_SIMDUnit re (sz 8) (-1316856l) 759969l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_1___round #v_SIMDUnit re (sz 9) (-210977l) 2389356l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_1___round #v_SIMDUnit re (sz 10) (-3249728l) 1653064l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_1___round #v_SIMDUnit re (sz 11) (-8578l) (-3724342l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_1___round #v_SIMDUnit re (sz 12) 3958618l 904516l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_1___round #v_SIMDUnit re (sz 13) (-1100098l) 44288l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_1___round #v_SIMDUnit re (sz 14) 3097992l 508951l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_1___round #v_SIMDUnit re (sz 15) 264944l (-3343383l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_1___round #v_SIMDUnit re (sz 16) (-1430430l) 1852771l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_1___round #v_SIMDUnit re (sz 17) 1349076l (-381987l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_1___round #v_SIMDUnit re (sz 18) (-1308169l) (-22981l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_1___round #v_SIMDUnit re (sz 19) (-1228525l) (-671102l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_1___round #v_SIMDUnit re (sz 20) (-2477047l) (-411027l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_1___round #v_SIMDUnit re (sz 21) (-3693493l) (-2967645l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_1___round #v_SIMDUnit re (sz 22) 2715295l 2147896l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_1___round #v_SIMDUnit re (sz 23) (-983419l) 3412210l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_1___round #v_SIMDUnit re (sz 24) 126922l (-3632928l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_1___round #v_SIMDUnit re (sz 25) (-3157330l) (-3190144l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_1___round #v_SIMDUnit re (sz 26) (-1000202l) (-4083598l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_1___round #v_SIMDUnit re (sz 27) 1939314l (-1257611l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_1___round #v_SIMDUnit re (sz 28) (-1585221l) 2176455l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_1___round #v_SIMDUnit re (sz 29) 3475950l (-1452451l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_1___round #v_SIMDUnit re (sz 30) (-3041255l) (-3677745l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_1___round #v_SIMDUnit re (sz 31) (-1528703l) (-3930395l)
  in
  re

let invert_ntt_at_layer_2___round
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      (index: usize)
      (zeta: i32)
     =
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    {
      re with
      Libcrux_ml_dsa.Polynomial.f_simd_units
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_dsa.Polynomial.f_simd_units
        index
        (Libcrux_ml_dsa.Simd.Traits.f_invert_ntt_at_layer_2_ #v_SIMDUnit
            #FStar.Tactics.Typeclasses.solve
            (re.Libcrux_ml_dsa.Polynomial.f_simd_units.[ index ] <: v_SIMDUnit)
            zeta
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
    invert_ntt_at_layer_2___round #v_SIMDUnit re (sz 0) (-2797779l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_2___round #v_SIMDUnit re (sz 1) 2071892l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_2___round #v_SIMDUnit re (sz 2) (-2556880l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_2___round #v_SIMDUnit re (sz 3) 3900724l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_2___round #v_SIMDUnit re (sz 4) 3881043l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_2___round #v_SIMDUnit re (sz 5) 954230l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_2___round #v_SIMDUnit re (sz 6) 531354l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_2___round #v_SIMDUnit re (sz 7) 811944l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_2___round #v_SIMDUnit re (sz 8) 3699596l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_2___round #v_SIMDUnit re (sz 9) (-1600420l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_2___round #v_SIMDUnit re (sz 10) (-2140649l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_2___round #v_SIMDUnit re (sz 11) 3507263l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_2___round #v_SIMDUnit re (sz 12) (-3821735l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_2___round #v_SIMDUnit re (sz 13) 3505694l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_2___round #v_SIMDUnit re (sz 14) (-1643818l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_2___round #v_SIMDUnit re (sz 15) (-1699267l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_2___round #v_SIMDUnit re (sz 16) (-539299l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_2___round #v_SIMDUnit re (sz 17) 2348700l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_2___round #v_SIMDUnit re (sz 18) (-300467l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_2___round #v_SIMDUnit re (sz 19) 3539968l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_2___round #v_SIMDUnit re (sz 20) (-2867647l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_2___round #v_SIMDUnit re (sz 21) 3574422l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_2___round #v_SIMDUnit re (sz 22) (-3043716l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_2___round #v_SIMDUnit re (sz 23) (-3861115l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_2___round #v_SIMDUnit re (sz 24) 3915439l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_2___round #v_SIMDUnit re (sz 25) (-2537516l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_2___round #v_SIMDUnit re (sz 26) (-3592148l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_2___round #v_SIMDUnit re (sz 27) (-1661693l)
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_2___round #v_SIMDUnit re (sz 28) 3530437l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_2___round #v_SIMDUnit re (sz 29) 3077325l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_2___round #v_SIMDUnit re (sz 30) 95776l
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    invert_ntt_at_layer_2___round #v_SIMDUnit re (sz 31) 2706023l
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
