module Libcrux_ml_dsa.Simd.Avx2.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let ntt_at_layer_7_and_6___mul
      (re: t_Array u8 (sz 32))
      (index: usize)
      (zeta: u8)
      (step_by: usize)
      (field_modulus inverse_of_modulus_mod_montgomery_r: u8)
     =
  let prod02:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_mul_epi32 (re.[ index +! step_by <: usize ] <: u8) zeta
  in
  let prod13:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_mul_epi32 (Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32
          245l
          (re.[ index +! step_by <: usize ] <: u8)
        <:
        u8)
      (Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 245l zeta <: u8)
  in
  let k02:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_mul_epi32 prod02 inverse_of_modulus_mod_montgomery_r
  in
  let k13:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_mul_epi32 prod13 inverse_of_modulus_mod_montgomery_r
  in
  let c02:u8 = Libcrux_intrinsics.Avx2_extract.mm256_mul_epi32 k02 field_modulus in
  let c13:u8 = Libcrux_intrinsics.Avx2_extract.mm256_mul_epi32 k13 field_modulus in
  let res02:u8 = Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 prod02 c02 in
  let res13:u8 = Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 prod13 c13 in
  let res02_shifted:u8 = Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 245l res02 in
  let t:u8 = Libcrux_intrinsics.Avx2_extract.mm256_blend_epi32 170l res02_shifted res13 in
  let re:t_Array u8 (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (index +! step_by <: usize)
      (Libcrux_ml_dsa.Simd.Avx2.Arithmetic.subtract (re.[ index ] <: u8) t <: u8)
  in
  let re:t_Array u8 (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      index
      (Libcrux_ml_dsa.Simd.Avx2.Arithmetic.add (re.[ index ] <: u8) t <: u8)
  in
  re

let butterfly_2_ (a b: u8) (zeta_a0 zeta_a1 zeta_a2 zeta_a3 zeta_b0 zeta_b1 zeta_b2 zeta_b3: i32) =
  let a_shuffled:u8 = Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 216l a in
  let b_shuffled:u8 = Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 216l b in
  let summands:u8 = Libcrux_intrinsics.Avx2_extract.mm256_unpacklo_epi64 a_shuffled b_shuffled in
  let zeta_multiplicands:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_unpackhi_epi64 a_shuffled b_shuffled
  in
  let zetas:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 zeta_b3
      zeta_b2
      zeta_a3
      zeta_a2
      zeta_b1
      zeta_b0
      zeta_a1
      zeta_a0
  in
  let zeta_products:u8 =
    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply zeta_multiplicands zetas
  in
  let add_terms:u8 = Libcrux_ml_dsa.Simd.Avx2.Arithmetic.add summands zeta_products in
  let sub_terms:u8 = Libcrux_ml_dsa.Simd.Avx2.Arithmetic.subtract summands zeta_products in
  let a_terms_shuffled:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_unpacklo_epi64 add_terms sub_terms
  in
  let b_terms_shuffled:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_unpackhi_epi64 add_terms sub_terms
  in
  let a_out:u8 = Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 216l a_terms_shuffled in
  let b_out:u8 = Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 216l b_terms_shuffled in
  a_out, b_out <: (u8 & u8)

let butterfly_4_ (a b: u8) (zeta_a0 zeta_a1 zeta_b0 zeta_b1: i32) =
  let summands:u8 = Libcrux_intrinsics.Avx2_extract.mm256_unpacklo_epi64 a b in
  let zeta_multiplicands:u8 = Libcrux_intrinsics.Avx2_extract.mm256_unpackhi_epi64 a b in
  let zetas:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 zeta_b1
      zeta_b1
      zeta_a1
      zeta_a1
      zeta_b0
      zeta_b0
      zeta_a0
      zeta_a0
  in
  let zeta_products:u8 =
    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply zeta_multiplicands zetas
  in
  let add_terms:u8 = Libcrux_ml_dsa.Simd.Avx2.Arithmetic.add summands zeta_products in
  let sub_terms:u8 = Libcrux_ml_dsa.Simd.Avx2.Arithmetic.subtract summands zeta_products in
  let a_out:u8 = Libcrux_intrinsics.Avx2_extract.mm256_unpacklo_epi64 add_terms sub_terms in
  let b_out:u8 = Libcrux_intrinsics.Avx2_extract.mm256_unpackhi_epi64 add_terms sub_terms in
  a_out, b_out <: (u8 & u8)

let butterfly_8_ (a b: u8) (zeta0 zeta1: i32) =
  let summands:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_m128i (Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128
          b
        <:
        u8)
      (Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 a <: u8)
  in
  let zeta_multiplicands:u8 = Libcrux_intrinsics.Avx2_extract.mm256_permute2x128_si256 19l b a in
  let zetas:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 zeta1 zeta1 zeta1 zeta1 zeta0 zeta0 zeta0 zeta0
  in
  let zeta_products:u8 =
    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply zeta_multiplicands zetas
  in
  let add_terms:u8 = Libcrux_ml_dsa.Simd.Avx2.Arithmetic.add summands zeta_products in
  let sub_terms:u8 = Libcrux_ml_dsa.Simd.Avx2.Arithmetic.subtract summands zeta_products in
  let a_out:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_m128i (Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128
          sub_terms
        <:
        u8)
      (Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 add_terms <: u8)
  in
  let b_out:u8 = Libcrux_intrinsics.Avx2_extract.mm256_permute2x128_si256 19l sub_terms add_terms in
  a_out, b_out <: (u8 & u8)

let ntt_at_layer_0___round
      (re: t_Array u8 (sz 32))
      (index: usize)
      (zeta_0_ zeta_1_ zeta_2_ zeta_3_ zeta_4_ zeta_5_ zeta_6_ zeta_7_: i32)
     =
  let a, b:(u8 & u8) =
    butterfly_2_ (re.[ index ] <: u8) (re.[ index +! sz 1 <: usize ] <: u8) zeta_0_ zeta_1_ zeta_2_
      zeta_3_ zeta_4_ zeta_5_ zeta_6_ zeta_7_
  in
  let re:t_Array u8 (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re index a
  in
  let re:t_Array u8 (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re (index +! sz 1 <: usize) b
  in
  re

let ntt_at_layer_0_ (re: t_Array u8 (sz 32)) =
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_0___round re (sz 0) 2091667l 3407706l 2316500l 3817976l (-3342478l) 2244091l
      (-2446433l) (-3562462l)
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_0___round re (sz 2) 266997l 2434439l (-1235728l) 3513181l (-3520352l) (-3759364l)
      (-1197226l) (-3193378l)
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_0___round re (sz 4) 900702l 1859098l 909542l 819034l 495491l (-1613174l) (-43260l)
      (-522500l)
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_0___round re (sz 6) (-655327l) (-3122442l) 2031748l 3207046l (-3556995l) (-525098l)
      (-768622l) (-3595838l)
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_0___round re (sz 8) 342297l 286988l (-2437823l) 4108315l 3437287l (-3342277l)
      1735879l 203044l
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_0___round re (sz 10) 2842341l 2691481l (-2590150l) 1265009l 4055324l 1247620l
      2486353l 1595974l
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_0___round re (sz 12) (-3767016l) 1250494l 2635921l (-3548272l) (-2994039l) 1869119l
      1903435l (-1050970l)
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_0___round re (sz 14) (-1333058l) 1237275l (-3318210l) (-1430225l) (-451100l)
      1312455l 3306115l (-1962642l)
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_0___round re (sz 16) (-1279661l) 1917081l (-2546312l) (-1374803l) 1500165l 777191l
      2235880l 3406031l
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_0___round re (sz 18) (-542412l) (-2831860l) (-1671176l) (-1846953l) (-2584293l)
      (-3724270l) 594136l (-3776993l)
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_0___round re (sz 20) (-2013608l) 2432395l 2454455l (-164721l) 1957272l 3369112l
      185531l (-1207385l)
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_0___round re (sz 22) (-3183426l) 162844l 1616392l 3014001l 810149l 1652634l
      (-3694233l) (-1799107l)
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_0___round re (sz 24) (-3038916l) 3523897l 3866901l 269760l 2213111l (-975884l)
      1717735l 472078l
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_0___round re (sz 26) (-426683l) 1723600l (-1803090l) 1910376l (-1667432l)
      (-1104333l) (-260646l) (-3833893l)
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_0___round re (sz 28) (-2939036l) (-2235985l) (-420899l) (-2286327l) 183443l
      (-976891l) 1612842l (-3545687l)
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_0___round re (sz 30) (-554416l) 3919660l (-48306l) (-1362209l) 3937738l 1400424l
      (-846154l) 1976782l
  in
  re

let ntt_at_layer_1___round
      (re: t_Array u8 (sz 32))
      (index: usize)
      (zeta_0_ zeta_1_ zeta_2_ zeta_3_: i32)
     =
  let a, b:(u8 & u8) =
    butterfly_4_ (re.[ index ] <: u8)
      (re.[ index +! sz 1 <: usize ] <: u8)
      zeta_0_
      zeta_1_
      zeta_2_
      zeta_3_
  in
  let re:t_Array u8 (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re index a
  in
  let re:t_Array u8 (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re (index +! sz 1 <: usize) b
  in
  re

let ntt_at_layer_1_ (re: t_Array u8 (sz 32)) =
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_1___round re (sz 0) (-3930395l) (-1528703l) (-3677745l) (-3041255l)
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_1___round re (sz 2) (-1452451l) 3475950l 2176455l (-1585221l)
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_1___round re (sz 4) (-1257611l) 1939314l (-4083598l) (-1000202l)
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_1___round re (sz 6) (-3190144l) (-3157330l) (-3632928l) 126922l
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_1___round re (sz 8) 3412210l (-983419l) 2147896l 2715295l
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_1___round re (sz 10) (-2967645l) (-3693493l) (-411027l) (-2477047l)
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_1___round re (sz 12) (-671102l) (-1228525l) (-22981l) (-1308169l)
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_1___round re (sz 14) (-381987l) 1349076l 1852771l (-1430430l)
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_1___round re (sz 16) (-3343383l) 264944l 508951l 3097992l
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_1___round re (sz 18) 44288l (-1100098l) 904516l 3958618l
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_1___round re (sz 20) (-3724342l) (-8578l) 1653064l (-3249728l)
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_1___round re (sz 22) 2389356l (-210977l) 759969l (-1316856l)
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_1___round re (sz 24) 189548l (-3553272l) 3159746l (-1851402l)
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_1___round re (sz 26) (-2409325l) (-177440l) 1315589l 1341330l
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_1___round re (sz 28) 1285669l (-1584928l) (-812732l) (-1439742l)
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_1___round re (sz 30) (-3019102l) (-3881060l) (-3628969l) 3839961l
  in
  re

let ntt_at_layer_2___round (re: t_Array u8 (sz 32)) (index: usize) (zeta_0_ zeta_1_: i32) =
  let a, b:(u8 & u8) =
    butterfly_8_ (re.[ index ] <: u8) (re.[ index +! sz 1 <: usize ] <: u8) zeta_0_ zeta_1_
  in
  let re:t_Array u8 (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re index a
  in
  let re:t_Array u8 (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re (index +! sz 1 <: usize) b
  in
  re

let ntt_at_layer_2_ (re: t_Array u8 (sz 32)) =
  let re:t_Array u8 (sz 32) = ntt_at_layer_2___round re (sz 0) 2706023l 95776l in
  let re:t_Array u8 (sz 32) = ntt_at_layer_2___round re (sz 2) 3077325l 3530437l in
  let re:t_Array u8 (sz 32) = ntt_at_layer_2___round re (sz 4) (-1661693l) (-3592148l) in
  let re:t_Array u8 (sz 32) = ntt_at_layer_2___round re (sz 6) (-2537516l) 3915439l in
  let re:t_Array u8 (sz 32) = ntt_at_layer_2___round re (sz 8) (-3861115l) (-3043716l) in
  let re:t_Array u8 (sz 32) = ntt_at_layer_2___round re (sz 10) 3574422l (-2867647l) in
  let re:t_Array u8 (sz 32) = ntt_at_layer_2___round re (sz 12) 3539968l (-300467l) in
  let re:t_Array u8 (sz 32) = ntt_at_layer_2___round re (sz 14) 2348700l (-539299l) in
  let re:t_Array u8 (sz 32) = ntt_at_layer_2___round re (sz 16) (-1699267l) (-1643818l) in
  let re:t_Array u8 (sz 32) = ntt_at_layer_2___round re (sz 18) 3505694l (-3821735l) in
  let re:t_Array u8 (sz 32) = ntt_at_layer_2___round re (sz 20) 3507263l (-2140649l) in
  let re:t_Array u8 (sz 32) = ntt_at_layer_2___round re (sz 22) (-1600420l) 3699596l in
  let re:t_Array u8 (sz 32) = ntt_at_layer_2___round re (sz 24) 811944l 531354l in
  let re:t_Array u8 (sz 32) = ntt_at_layer_2___round re (sz 26) 954230l 3881043l in
  let re:t_Array u8 (sz 32) = ntt_at_layer_2___round re (sz 28) 3900724l (-2556880l) in
  let re:t_Array u8 (sz 32) = ntt_at_layer_2___round re (sz 30) 2071892l (-2797779l) in
  re

let ntt_at_layer_7_and_6_ (re: t_Array u8 (sz 32)) =
  let field_modulus:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
  in
  let inverse_of_modulus_mod_montgomery_r:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (cast (Libcrux_ml_dsa.Simd.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
            <:
            u64)
        <:
        i32)
  in
  let zeta7:u8 = Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 25847l in
  let zeta60:u8 = Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (-2608894l) in
  let zeta61:u8 = Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (-518909l) in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_7_and_6___mul re
      (sz 0)
      zeta7
      ntt_at_layer_7_and_6___STEP_BY_7_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_7_and_6___mul re
      (sz 0 +! sz 1 <: usize)
      zeta7
      ntt_at_layer_7_and_6___STEP_BY_7_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_7_and_6___mul re
      (sz 0 +! sz 2 <: usize)
      zeta7
      ntt_at_layer_7_and_6___STEP_BY_7_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_7_and_6___mul re
      (sz 0 +! sz 3 <: usize)
      zeta7
      ntt_at_layer_7_and_6___STEP_BY_7_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let _:Prims.unit = () in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_7_and_6___mul re
      (sz 8)
      zeta7
      ntt_at_layer_7_and_6___STEP_BY_7_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_7_and_6___mul re
      (sz 8 +! sz 1 <: usize)
      zeta7
      ntt_at_layer_7_and_6___STEP_BY_7_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_7_and_6___mul re
      (sz 8 +! sz 2 <: usize)
      zeta7
      ntt_at_layer_7_and_6___STEP_BY_7_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_7_and_6___mul re
      (sz 8 +! sz 3 <: usize)
      zeta7
      ntt_at_layer_7_and_6___STEP_BY_7_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let _:Prims.unit = () in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_7_and_6___mul re
      (sz 0)
      zeta60
      ntt_at_layer_7_and_6___STEP_BY_6_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_7_and_6___mul re
      (sz 0 +! sz 1 <: usize)
      zeta60
      ntt_at_layer_7_and_6___STEP_BY_6_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_7_and_6___mul re
      (sz 0 +! sz 2 <: usize)
      zeta60
      ntt_at_layer_7_and_6___STEP_BY_6_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_7_and_6___mul re
      (sz 0 +! sz 3 <: usize)
      zeta60
      ntt_at_layer_7_and_6___STEP_BY_6_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let _:Prims.unit = () in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_7_and_6___mul re
      (sz 16)
      zeta61
      ntt_at_layer_7_and_6___STEP_BY_6_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_7_and_6___mul re
      (sz 16 +! sz 1 <: usize)
      zeta61
      ntt_at_layer_7_and_6___STEP_BY_6_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_7_and_6___mul re
      (sz 16 +! sz 2 <: usize)
      zeta61
      ntt_at_layer_7_and_6___STEP_BY_6_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_7_and_6___mul re
      (sz 16 +! sz 3 <: usize)
      zeta61
      ntt_at_layer_7_and_6___STEP_BY_6_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let _:Prims.unit = () in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_7_and_6___mul re
      (sz 4)
      zeta7
      ntt_at_layer_7_and_6___STEP_BY_7_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_7_and_6___mul re
      (sz 4 +! sz 1 <: usize)
      zeta7
      ntt_at_layer_7_and_6___STEP_BY_7_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_7_and_6___mul re
      (sz 4 +! sz 2 <: usize)
      zeta7
      ntt_at_layer_7_and_6___STEP_BY_7_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_7_and_6___mul re
      (sz 4 +! sz 3 <: usize)
      zeta7
      ntt_at_layer_7_and_6___STEP_BY_7_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let _:Prims.unit = () in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_7_and_6___mul re
      (sz 12)
      zeta7
      ntt_at_layer_7_and_6___STEP_BY_7_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_7_and_6___mul re
      (sz 12 +! sz 1 <: usize)
      zeta7
      ntt_at_layer_7_and_6___STEP_BY_7_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_7_and_6___mul re
      (sz 12 +! sz 2 <: usize)
      zeta7
      ntt_at_layer_7_and_6___STEP_BY_7_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_7_and_6___mul re
      (sz 12 +! sz 3 <: usize)
      zeta7
      ntt_at_layer_7_and_6___STEP_BY_7_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let _:Prims.unit = () in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_7_and_6___mul re
      (sz 4)
      zeta60
      ntt_at_layer_7_and_6___STEP_BY_6_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_7_and_6___mul re
      (sz 4 +! sz 1 <: usize)
      zeta60
      ntt_at_layer_7_and_6___STEP_BY_6_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_7_and_6___mul re
      (sz 4 +! sz 2 <: usize)
      zeta60
      ntt_at_layer_7_and_6___STEP_BY_6_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_7_and_6___mul re
      (sz 4 +! sz 3 <: usize)
      zeta60
      ntt_at_layer_7_and_6___STEP_BY_6_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let _:Prims.unit = () in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_7_and_6___mul re
      (sz 20)
      zeta61
      ntt_at_layer_7_and_6___STEP_BY_6_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_7_and_6___mul re
      (sz 20 +! sz 1 <: usize)
      zeta61
      ntt_at_layer_7_and_6___STEP_BY_6_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_7_and_6___mul re
      (sz 20 +! sz 2 <: usize)
      zeta61
      ntt_at_layer_7_and_6___STEP_BY_6_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array u8 (sz 32) =
    ntt_at_layer_7_and_6___mul re
      (sz 20 +! sz 3 <: usize)
      zeta61
      ntt_at_layer_7_and_6___STEP_BY_6_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let _:Prims.unit = () in
  re

let ntt_at_layer_5_to_3___round
      (v_STEP v_STEP_BY: usize)
      (re: t_Array u8 (sz 32))
      (index: usize)
      (zeta: i32)
     =
  let rhs:u8 = Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 zeta in
  let offset:usize =
    ((index *! v_STEP <: usize) *! sz 2 <: usize) /!
    Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT
  in
  let re:t_Array u8 (sz 32) =
    Rust_primitives.Hax.Folds.fold_range offset
      (offset +! v_STEP_BY <: usize)
      (fun re temp_1_ ->
          let re:t_Array u8 (sz 32) = re in
          let _:usize = temp_1_ in
          true)
      re
      (fun re j ->
          let re:t_Array u8 (sz 32) = re in
          let j:usize = j in
          let t:u8 =
            Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply (re.[ j +! v_STEP_BY <: usize ]
                <:
                u8)
              rhs
          in
          let re:t_Array u8 (sz 32) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
              (j +! v_STEP_BY <: usize)
              (Libcrux_ml_dsa.Simd.Avx2.Arithmetic.subtract (re.[ j ] <: u8) t <: u8)
          in
          let re:t_Array u8 (sz 32) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
              j
              (Libcrux_ml_dsa.Simd.Avx2.Arithmetic.add (re.[ j ] <: u8) t <: u8)
          in
          re)
  in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  re

let ntt_at_layer_5_to_3_ (re: t_Array u8 (sz 32)) =
  let re:t_Array u8 (sz 32) = ntt_at_layer_5_to_3___round (sz 32) (sz 4) re (sz 0) 237124l in
  let re:t_Array u8 (sz 32) = ntt_at_layer_5_to_3___round (sz 32) (sz 4) re (sz 1) (-777960l) in
  let re:t_Array u8 (sz 32) = ntt_at_layer_5_to_3___round (sz 32) (sz 4) re (sz 2) (-876248l) in
  let re:t_Array u8 (sz 32) = ntt_at_layer_5_to_3___round (sz 32) (sz 4) re (sz 3) 466468l in
  let _:Prims.unit = () in
  let re:t_Array u8 (sz 32) = ntt_at_layer_5_to_3___round (sz 16) (sz 2) re (sz 0) 1826347l in
  let re:t_Array u8 (sz 32) = ntt_at_layer_5_to_3___round (sz 16) (sz 2) re (sz 1) 2353451l in
  let re:t_Array u8 (sz 32) = ntt_at_layer_5_to_3___round (sz 16) (sz 2) re (sz 2) (-359251l) in
  let re:t_Array u8 (sz 32) = ntt_at_layer_5_to_3___round (sz 16) (sz 2) re (sz 3) (-2091905l) in
  let re:t_Array u8 (sz 32) = ntt_at_layer_5_to_3___round (sz 16) (sz 2) re (sz 4) 3119733l in
  let re:t_Array u8 (sz 32) = ntt_at_layer_5_to_3___round (sz 16) (sz 2) re (sz 5) (-2884855l) in
  let re:t_Array u8 (sz 32) = ntt_at_layer_5_to_3___round (sz 16) (sz 2) re (sz 6) 3111497l in
  let re:t_Array u8 (sz 32) = ntt_at_layer_5_to_3___round (sz 16) (sz 2) re (sz 7) 2680103l in
  let _:Prims.unit = () in
  let re:t_Array u8 (sz 32) = ntt_at_layer_5_to_3___round (sz 8) (sz 1) re (sz 0) 2725464l in
  let re:t_Array u8 (sz 32) = ntt_at_layer_5_to_3___round (sz 8) (sz 1) re (sz 1) 1024112l in
  let re:t_Array u8 (sz 32) = ntt_at_layer_5_to_3___round (sz 8) (sz 1) re (sz 2) (-1079900l) in
  let re:t_Array u8 (sz 32) = ntt_at_layer_5_to_3___round (sz 8) (sz 1) re (sz 3) 3585928l in
  let re:t_Array u8 (sz 32) = ntt_at_layer_5_to_3___round (sz 8) (sz 1) re (sz 4) (-549488l) in
  let re:t_Array u8 (sz 32) = ntt_at_layer_5_to_3___round (sz 8) (sz 1) re (sz 5) (-1119584l) in
  let re:t_Array u8 (sz 32) = ntt_at_layer_5_to_3___round (sz 8) (sz 1) re (sz 6) 2619752l in
  let re:t_Array u8 (sz 32) = ntt_at_layer_5_to_3___round (sz 8) (sz 1) re (sz 7) (-2108549l) in
  let re:t_Array u8 (sz 32) = ntt_at_layer_5_to_3___round (sz 8) (sz 1) re (sz 8) (-2118186l) in
  let re:t_Array u8 (sz 32) = ntt_at_layer_5_to_3___round (sz 8) (sz 1) re (sz 9) (-3859737l) in
  let re:t_Array u8 (sz 32) = ntt_at_layer_5_to_3___round (sz 8) (sz 1) re (sz 10) (-1399561l) in
  let re:t_Array u8 (sz 32) = ntt_at_layer_5_to_3___round (sz 8) (sz 1) re (sz 11) (-3277672l) in
  let re:t_Array u8 (sz 32) = ntt_at_layer_5_to_3___round (sz 8) (sz 1) re (sz 12) 1757237l in
  let re:t_Array u8 (sz 32) = ntt_at_layer_5_to_3___round (sz 8) (sz 1) re (sz 13) (-19422l) in
  let re:t_Array u8 (sz 32) = ntt_at_layer_5_to_3___round (sz 8) (sz 1) re (sz 14) 4010497l in
  let re:t_Array u8 (sz 32) = ntt_at_layer_5_to_3___round (sz 8) (sz 1) re (sz 15) 280005l in
  let _:Prims.unit = () in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  re

let ntt (re: t_Array u8 (sz 32)) =
  let re:t_Array u8 (sz 32) = ntt_at_layer_7_and_6_ re in
  let re:t_Array u8 (sz 32) = ntt_at_layer_5_to_3_ re in
  let re:t_Array u8 (sz 32) = ntt_at_layer_2_ re in
  let re:t_Array u8 (sz 32) = ntt_at_layer_1_ re in
  let re:t_Array u8 (sz 32) = ntt_at_layer_0_ re in
  let _:Prims.unit = () in
  re
