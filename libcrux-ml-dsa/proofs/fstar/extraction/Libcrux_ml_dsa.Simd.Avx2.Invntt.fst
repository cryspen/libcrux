module Libcrux_ml_dsa.Simd.Avx2.Invntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let simd_unit_invert_ntt_at_layer_0_
      (simd_unit0 simd_unit1: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (zeta00 zeta01 zeta02 zeta03 zeta10 zeta11 zeta12 zeta13: i32)
     =
  let a_shuffled:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 216l simd_unit0
  in
  let b_shuffled:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 216l simd_unit1
  in
  let lo_values:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_unpacklo_epi64 a_shuffled b_shuffled
  in
  let hi_values:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_unpackhi_epi64 a_shuffled b_shuffled
  in
  let sums:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.add lo_values hi_values
  in
  let differences:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.subtract hi_values lo_values
  in
  let zetas:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 zeta13
      zeta12
      zeta03
      zeta02
      zeta11
      zeta10
      zeta01
      zeta00
  in
  let products:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply differences zetas
  in
  let a_shuffled:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_unpacklo_epi64 sums products
  in
  let b_shuffled:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_unpackhi_epi64 sums products
  in
  let a:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 216l a_shuffled
  in
  let b:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 216l b_shuffled
  in
  a, b <: (Libcrux_intrinsics.Avx2_extract.t_Vec256 & Libcrux_intrinsics.Avx2_extract.t_Vec256)

let invert_ntt_at_layer_0___round
      (re: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
      (index: usize)
      (zeta00 zeta01 zeta02 zeta03 zeta10 zeta11 zeta12 zeta13: i32)
     =
  let lhs, lhs_1_:(Libcrux_intrinsics.Avx2_extract.t_Vec256 &
    Libcrux_intrinsics.Avx2_extract.t_Vec256) =
    simd_unit_invert_ntt_at_layer_0_ (re.[ index ] <: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (re.[ index +! sz 1 <: usize ] <: Libcrux_intrinsics.Avx2_extract.t_Vec256) zeta00 zeta01
      zeta02 zeta03 zeta10 zeta11 zeta12 zeta13
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re index lhs
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re (index +! sz 1 <: usize) lhs_1_
  in
  let _:Prims.unit = () in
  re

let invert_ntt_at_layer_0_ (re: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32)) =
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_0___round re (sz 0) 1976782l (-846154l) 1400424l 3937738l (-1362209l)
      (-48306l) 3919660l (-554416l)
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_0___round re (sz 2) (-3545687l) 1612842l (-976891l) 183443l (-2286327l)
      (-420899l) (-2235985l) (-2939036l)
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_0___round re (sz 4) (-3833893l) (-260646l) (-1104333l) (-1667432l) 1910376l
      (-1803090l) 1723600l (-426683l)
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_0___round re (sz 6) 472078l 1717735l (-975884l) 2213111l 269760l 3866901l
      3523897l (-3038916l)
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_0___round re (sz 8) (-1799107l) (-3694233l) 1652634l 810149l 3014001l
      1616392l 162844l (-3183426l)
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_0___round re (sz 10) (-1207385l) 185531l 3369112l 1957272l (-164721l)
      2454455l 2432395l (-2013608l)
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_0___round re (sz 12) (-3776993l) 594136l (-3724270l) (-2584293l) (-1846953l)
      (-1671176l) (-2831860l) (-542412l)
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_0___round re (sz 14) 3406031l 2235880l 777191l 1500165l (-1374803l)
      (-2546312l) 1917081l (-1279661l)
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_0___round re (sz 16) (-1962642l) 3306115l 1312455l (-451100l) (-1430225l)
      (-3318210l) 1237275l (-1333058l)
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_0___round re (sz 18) (-1050970l) 1903435l 1869119l (-2994039l) (-3548272l)
      2635921l 1250494l (-3767016l)
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_0___round re (sz 20) 1595974l 2486353l 1247620l 4055324l 1265009l
      (-2590150l) 2691481l 2842341l
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_0___round re (sz 22) 203044l 1735879l (-3342277l) 3437287l 4108315l
      (-2437823l) 286988l 342297l
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_0___round re (sz 24) (-3595838l) (-768622l) (-525098l) (-3556995l) 3207046l
      2031748l (-3122442l) (-655327l)
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_0___round re (sz 26) (-522500l) (-43260l) (-1613174l) 495491l 819034l
      909542l 1859098l 900702l
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_0___round re (sz 28) (-3193378l) (-1197226l) (-3759364l) (-3520352l)
      3513181l (-1235728l) 2434439l 266997l
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_0___round re (sz 30) (-3562462l) (-2446433l) 2244091l (-3342478l) 3817976l
      2316500l 3407706l 2091667l
  in
  re

let simd_unit_invert_ntt_at_layer_1_
      (simd_unit0 simd_unit1: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (zeta00 zeta01 zeta10 zeta11: i32)
     =
  let lo_values:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_unpacklo_epi64 simd_unit0 simd_unit1
  in
  let hi_values:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_unpackhi_epi64 simd_unit0 simd_unit1
  in
  let sums:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.add lo_values hi_values
  in
  let differences:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.subtract hi_values lo_values
  in
  let zetas:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 zeta11
      zeta11
      zeta01
      zeta01
      zeta10
      zeta10
      zeta00
      zeta00
  in
  let products:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply differences zetas
  in
  let a:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_unpacklo_epi64 sums products
  in
  let b:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_unpackhi_epi64 sums products
  in
  a, b <: (Libcrux_intrinsics.Avx2_extract.t_Vec256 & Libcrux_intrinsics.Avx2_extract.t_Vec256)

let invert_ntt_at_layer_1___round
      (re: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
      (index: usize)
      (zeta_00_ zeta_01_ zeta_10_ zeta_11_: i32)
     =
  let lhs, lhs_1_:(Libcrux_intrinsics.Avx2_extract.t_Vec256 &
    Libcrux_intrinsics.Avx2_extract.t_Vec256) =
    simd_unit_invert_ntt_at_layer_1_ (re.[ index ] <: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (re.[ index +! sz 1 <: usize ] <: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      zeta_00_
      zeta_01_
      zeta_10_
      zeta_11_
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re index lhs
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re (index +! sz 1 <: usize) lhs_1_
  in
  let _:Prims.unit = () in
  re

let invert_ntt_at_layer_1_ (re: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32)) =
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_1___round re (sz 0) 3839961l (-3628969l) (-3881060l) (-3019102l)
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_1___round re (sz 2) (-1439742l) (-812732l) (-1584928l) 1285669l
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_1___round re (sz 4) 1341330l 1315589l (-177440l) (-2409325l)
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_1___round re (sz 6) (-1851402l) 3159746l (-3553272l) 189548l
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_1___round re (sz 8) (-1316856l) 759969l (-210977l) 2389356l
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_1___round re (sz 10) (-3249728l) 1653064l (-8578l) (-3724342l)
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_1___round re (sz 12) 3958618l 904516l (-1100098l) 44288l
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_1___round re (sz 14) 3097992l 508951l 264944l (-3343383l)
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_1___round re (sz 16) (-1430430l) 1852771l 1349076l (-381987l)
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_1___round re (sz 18) (-1308169l) (-22981l) (-1228525l) (-671102l)
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_1___round re (sz 20) (-2477047l) (-411027l) (-3693493l) (-2967645l)
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_1___round re (sz 22) 2715295l 2147896l (-983419l) 3412210l
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_1___round re (sz 24) 126922l (-3632928l) (-3157330l) (-3190144l)
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_1___round re (sz 26) (-1000202l) (-4083598l) 1939314l (-1257611l)
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_1___round re (sz 28) (-1585221l) 2176455l 3475950l (-1452451l)
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_1___round re (sz 30) (-3041255l) (-3677745l) (-1528703l) (-3930395l)
  in
  re

let simd_unit_invert_ntt_at_layer_2_
      (simd_unit0 simd_unit1: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (zeta0 zeta1: i32)
     =
  let lo_values:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_permute2x128_si256 32l simd_unit0 simd_unit1
  in
  let hi_values:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_permute2x128_si256 49l simd_unit0 simd_unit1
  in
  let sums:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.add lo_values hi_values
  in
  let differences:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.subtract hi_values lo_values
  in
  let zetas:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 zeta1 zeta1 zeta1 zeta1 zeta0 zeta0 zeta0 zeta0
  in
  let products:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply differences zetas
  in
  let a:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_permute2x128_si256 32l sums products
  in
  let b:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_permute2x128_si256 49l sums products
  in
  a, b <: (Libcrux_intrinsics.Avx2_extract.t_Vec256 & Libcrux_intrinsics.Avx2_extract.t_Vec256)

let invert_ntt_at_layer_2___round
      (re: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
      (index: usize)
      (zeta1 zeta2: i32)
     =
  let lhs, lhs_1_:(Libcrux_intrinsics.Avx2_extract.t_Vec256 &
    Libcrux_intrinsics.Avx2_extract.t_Vec256) =
    simd_unit_invert_ntt_at_layer_2_ (re.[ index ] <: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (re.[ index +! sz 1 <: usize ] <: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      zeta1
      zeta2
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re index lhs
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re (index +! sz 1 <: usize) lhs_1_
  in
  let _:Prims.unit = () in
  re

let invert_ntt_at_layer_2_ (re: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32)) =
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_2___round re (sz 0) (-2797779l) 2071892l
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_2___round re (sz 2) (-2556880l) 3900724l
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_2___round re (sz 4) 3881043l 954230l
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_2___round re (sz 6) 531354l 811944l
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_2___round re (sz 8) 3699596l (-1600420l)
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_2___round re (sz 10) (-2140649l) 3507263l
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_2___round re (sz 12) (-3821735l) 3505694l
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_2___round re (sz 14) (-1643818l) (-1699267l)
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_2___round re (sz 16) (-539299l) 2348700l
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_2___round re (sz 18) (-300467l) 3539968l
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_2___round re (sz 20) (-2867647l) 3574422l
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_2___round re (sz 22) (-3043716l) (-3861115l)
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_2___round re (sz 24) 3915439l (-2537516l)
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_2___round re (sz 26) (-3592148l) (-1661693l)
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_2___round re (sz 28) 3530437l 3077325l
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    invert_ntt_at_layer_2___round re (sz 30) 95776l 2706023l
  in
  re

let outer_3_plus
      (v_OFFSET v_STEP_BY: usize)
      (v_ZETA: i32)
      (re: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
     =
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    Rust_primitives.Hax.Folds.fold_range v_OFFSET
      (v_OFFSET +! v_STEP_BY <: usize)
      (fun re temp_1_ ->
          let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) = re in
          let _:usize = temp_1_ in
          true)
      re
      (fun re j ->
          let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) = re in
          let j:usize = j in
          let a_minus_b:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
            Libcrux_ml_dsa.Simd.Avx2.Arithmetic.subtract (re.[ j +! v_STEP_BY <: usize ]
                <:
                Libcrux_intrinsics.Avx2_extract.t_Vec256)
              (re.[ j ] <: Libcrux_intrinsics.Avx2_extract.t_Vec256)
          in
          let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
              j
              (Libcrux_ml_dsa.Simd.Avx2.Arithmetic.add (re.[ j ]
                    <:
                    Libcrux_intrinsics.Avx2_extract.t_Vec256)
                  (re.[ j +! v_STEP_BY <: usize ] <: Libcrux_intrinsics.Avx2_extract.t_Vec256)
                <:
                Libcrux_intrinsics.Avx2_extract.t_Vec256)
          in
          let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
              (j +! v_STEP_BY <: usize)
              (Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply_by_constant a_minus_b v_ZETA
                <:
                Libcrux_intrinsics.Avx2_extract.t_Vec256)
          in
          re)
  in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  re

let invert_ntt_at_layer_3_ (re: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32)) =
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    outer_3_plus (sz 0) (sz 1) 280005l re
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    outer_3_plus (sz 2) (sz 1) 4010497l re
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    outer_3_plus (sz 4) (sz 1) (-19422l) re
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    outer_3_plus (sz 6) (sz 1) 1757237l re
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    outer_3_plus (sz 8) (sz 1) (-3277672l) re
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    outer_3_plus (sz 10) (sz 1) (-1399561l) re
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    outer_3_plus (sz 12) (sz 1) (-3859737l) re
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    outer_3_plus (sz 14) (sz 1) (-2118186l) re
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    outer_3_plus (sz 16) (sz 1) (-2108549l) re
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    outer_3_plus (sz 18) (sz 1) 2619752l re
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    outer_3_plus (sz 20) (sz 1) (-1119584l) re
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    outer_3_plus (sz 22) (sz 1) (-549488l) re
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    outer_3_plus (sz 24) (sz 1) 3585928l re
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    outer_3_plus (sz 26) (sz 1) (-1079900l) re
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    outer_3_plus (sz 28) (sz 1) 1024112l re
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    outer_3_plus (sz 30) (sz 1) 2725464l re
  in
  re

let invert_ntt_at_layer_4_ (re: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32)) =
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    outer_3_plus (sz 0) (sz 2) 2680103l re
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    outer_3_plus (sz 4) (sz 2) 3111497l re
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    outer_3_plus (sz 8) (sz 2) (-2884855l) re
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    outer_3_plus (sz 12) (sz 2) 3119733l re
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    outer_3_plus (sz 16) (sz 2) (-2091905l) re
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    outer_3_plus (sz 20) (sz 2) (-359251l) re
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    outer_3_plus (sz 24) (sz 2) 2353451l re
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    outer_3_plus (sz 28) (sz 2) 1826347l re
  in
  re

let invert_ntt_at_layer_5_ (re: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32)) =
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    outer_3_plus (sz 0) (sz 4) 466468l re
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    outer_3_plus (sz 8) (sz 4) (-876248l) re
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    outer_3_plus (sz 16) (sz 4) (-777960l) re
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    outer_3_plus (sz 24) (sz 4) 237124l re
  in
  re

let invert_ntt_at_layer_6_ (re: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32)) =
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    outer_3_plus (sz 0) (sz 8) (-518909l) re
  in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    outer_3_plus (sz 16) (sz 8) (-2608894l) re
  in
  re

let invert_ntt_at_layer_7_ (re: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32)) =
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    outer_3_plus (sz 0) (sz 16) 25847l re
  in
  re

let invert_ntt_montgomery (re: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32)) =
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) = invert_ntt_at_layer_0_ re in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) = invert_ntt_at_layer_1_ re in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) = invert_ntt_at_layer_2_ re in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) = invert_ntt_at_layer_3_ re in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) = invert_ntt_at_layer_4_ re in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) = invert_ntt_at_layer_5_ re in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) = invert_ntt_at_layer_6_ re in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) = invert_ntt_at_layer_7_ re in
  let _:Prims.unit = () in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #Libcrux_intrinsics.Avx2_extract.t_Vec256
          (re <: t_Slice Libcrux_intrinsics.Avx2_extract.t_Vec256)
        <:
        usize)
      (fun re temp_1_ ->
          let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) = re in
          let _:usize = temp_1_ in
          true)
      re
      (fun re i ->
          let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) = re in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
            i
            (Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply_by_constant (re.[ i ]
                  <:
                  Libcrux_intrinsics.Avx2_extract.t_Vec256)
                41978l
              <:
              Libcrux_intrinsics.Avx2_extract.t_Vec256)
          <:
          t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
  in
  re
