module Libcrux_ml_dsa.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

let v_ZETAS_TIMES_MONTGOMERY_R: t_Array i32 (sz 256) =
  let list =
    [
      0l; 25847l; (-2608894l); (-518909l); 237124l; (-777960l); (-876248l); 466468l; 1826347l;
      2353451l; (-359251l); (-2091905l); 3119733l; (-2884855l); 3111497l; 2680103l; 2725464l;
      1024112l; (-1079900l); 3585928l; (-549488l); (-1119584l); 2619752l; (-2108549l); (-2118186l);
      (-3859737l); (-1399561l); (-3277672l); 1757237l; (-19422l); 4010497l; 280005l; 2706023l;
      95776l; 3077325l; 3530437l; (-1661693l); (-3592148l); (-2537516l); 3915439l; (-3861115l);
      (-3043716l); 3574422l; (-2867647l); 3539968l; (-300467l); 2348700l; (-539299l); (-1699267l);
      (-1643818l); 3505694l; (-3821735l); 3507263l; (-2140649l); (-1600420l); 3699596l; 811944l;
      531354l; 954230l; 3881043l; 3900724l; (-2556880l); 2071892l; (-2797779l); (-3930395l);
      (-1528703l); (-3677745l); (-3041255l); (-1452451l); 3475950l; 2176455l; (-1585221l);
      (-1257611l); 1939314l; (-4083598l); (-1000202l); (-3190144l); (-3157330l); (-3632928l);
      126922l; 3412210l; (-983419l); 2147896l; 2715295l; (-2967645l); (-3693493l); (-411027l);
      (-2477047l); (-671102l); (-1228525l); (-22981l); (-1308169l); (-381987l); 1349076l; 1852771l;
      (-1430430l); (-3343383l); 264944l; 508951l; 3097992l; 44288l; (-1100098l); 904516l; 3958618l;
      (-3724342l); (-8578l); 1653064l; (-3249728l); 2389356l; (-210977l); 759969l; (-1316856l);
      189548l; (-3553272l); 3159746l; (-1851402l); (-2409325l); (-177440l); 1315589l; 1341330l;
      1285669l; (-1584928l); (-812732l); (-1439742l); (-3019102l); (-3881060l); (-3628969l);
      3839961l; 2091667l; 3407706l; 2316500l; 3817976l; (-3342478l); 2244091l; (-2446433l);
      (-3562462l); 266997l; 2434439l; (-1235728l); 3513181l; (-3520352l); (-3759364l); (-1197226l);
      (-3193378l); 900702l; 1859098l; 909542l; 819034l; 495491l; (-1613174l); (-43260l); (-522500l);
      (-655327l); (-3122442l); 2031748l; 3207046l; (-3556995l); (-525098l); (-768622l); (-3595838l);
      342297l; 286988l; (-2437823l); 4108315l; 3437287l; (-3342277l); 1735879l; 203044l; 2842341l;
      2691481l; (-2590150l); 1265009l; 4055324l; 1247620l; 2486353l; 1595974l; (-3767016l); 1250494l;
      2635921l; (-3548272l); (-2994039l); 1869119l; 1903435l; (-1050970l); (-1333058l); 1237275l;
      (-3318210l); (-1430225l); (-451100l); 1312455l; 3306115l; (-1962642l); (-1279661l); 1917081l;
      (-2546312l); (-1374803l); 1500165l; 777191l; 2235880l; 3406031l; (-542412l); (-2831860l);
      (-1671176l); (-1846953l); (-2584293l); (-3724270l); 594136l; (-3776993l); (-2013608l);
      2432395l; 2454455l; (-164721l); 1957272l; 3369112l; 185531l; (-1207385l); (-3183426l); 162844l;
      1616392l; 3014001l; 810149l; 1652634l; (-3694233l); (-1799107l); (-3038916l); 3523897l;
      3866901l; 269760l; 2213111l; (-975884l); 1717735l; 472078l; (-426683l); 1723600l; (-1803090l);
      1910376l; (-1667432l); (-1104333l); (-260646l); (-3833893l); (-2939036l); (-2235985l);
      (-420899l); (-2286327l); 183443l; (-976891l); 1612842l; (-3545687l); (-554416l); 3919660l;
      (-48306l); (-1362209l); 3937738l; 1400424l; (-846154l); 1976782l
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 256);
  Rust_primitives.Hax.array_of_list 256 list

val invert_ntt_at_layer_0_
      (#v_SIMDUnit: Type0)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (zeta_i: usize)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    : Prims.Pure (usize & Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      Prims.l_True
      (fun _ -> Prims.l_True)

val invert_ntt_at_layer_1_
      (#v_SIMDUnit: Type0)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (zeta_i: usize)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    : Prims.Pure (usize & Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      Prims.l_True
      (fun _ -> Prims.l_True)

val invert_ntt_at_layer_2_
      (#v_SIMDUnit: Type0)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (zeta_i: usize)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    : Prims.Pure (usize & Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      Prims.l_True
      (fun _ -> Prims.l_True)

val invert_ntt_at_layer_3_plus
      (#v_SIMDUnit: Type0)
      (v_LAYER: usize)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (zeta_i: usize)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    : Prims.Pure (usize & Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      Prims.l_True
      (fun _ -> Prims.l_True)

val invert_ntt_montgomery
      (#v_SIMDUnit: Type0)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    : Prims.Pure (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_at_layer_0_
      (#v_SIMDUnit: Type0)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (zeta_i: usize)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    : Prims.Pure (usize & Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_at_layer_1_
      (#v_SIMDUnit: Type0)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (zeta_i: usize)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    : Prims.Pure (usize & Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_at_layer_2_
      (#v_SIMDUnit: Type0)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (zeta_i: usize)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    : Prims.Pure (usize & Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_at_layer_3_plus
      (#v_SIMDUnit: Type0)
      (v_LAYER: usize)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (zeta_i: usize)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    : Prims.Pure (usize & Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt
      (#v_SIMDUnit: Type0)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    : Prims.Pure (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_multiply_montgomery
      (#v_SIMDUnit: Type0)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (lhs rhs: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    : Prims.Pure (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      Prims.l_True
      (fun _ -> Prims.l_True)
