module Libcrux_ml_dsa.Simd.Avx2.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let ntt_at_layer_7_and_6___mul
      (re: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      (index: usize)
      (zeta: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (step_by: usize)
      (field_modulus inverse_of_modulus_mod_montgomery_r: Libcrux_intrinsics.Avx2_extract.t_Vec256)
     =
  let prod02:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mul_epi32 (re.[ index +! step_by <: usize ]
        <:
        Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
      zeta
  in
  let prod13:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mul_epi32 (Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32
          (mk_i32 245)
          (re.[ index +! step_by <: usize ] <: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
            .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 (mk_i32 245) zeta
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let k02:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mul_epi32 prod02 inverse_of_modulus_mod_montgomery_r
  in
  let k13:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mul_epi32 prod13 inverse_of_modulus_mod_montgomery_r
  in
  let c02:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mul_epi32 k02 field_modulus
  in
  let c13:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mul_epi32 k13 field_modulus
  in
  let res02:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 prod02 c02
  in
  let res13:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 prod13 c13
  in
  let res02_shifted:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 (mk_i32 245) res02
  in
  let t:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_blend_epi32 (mk_i32 170) res02_shifted res13
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (index +! step_by <: usize)
      (re.[ index ] <: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (index +! step_by <: usize)
      ({
          (re.[ index +! step_by <: usize ] <: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256) with
          Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
          =
          Libcrux_ml_dsa.Simd.Avx2.Arithmetic.subtract (re.[ index +! step_by <: usize ]
              <:
              Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
              .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
            t
          <:
          Libcrux_intrinsics.Avx2_extract.t_Vec256
        }
        <:
        Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      index
      ({
          (re.[ index ] <: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256) with
          Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
          =
          Libcrux_ml_dsa.Simd.Avx2.Arithmetic.add (re.[ index ]
              <:
              Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
              .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
            t
          <:
          Libcrux_intrinsics.Avx2_extract.t_Vec256
        }
        <:
        Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
  in
  re

let butterfly_2_
      (re: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      (index: usize)
      (zeta_a0 zeta_a1 zeta_a2 zeta_a3 zeta_b0 zeta_b1 zeta_b2 zeta_b3: i32)
     =
  let a:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 (mk_i32 216)
      (re.[ index ] <: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
  in
  let b:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 (mk_i32 216)
      (re.[ index +! mk_usize 1 <: usize ] <: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
  in
  let summands:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_unpacklo_epi64 a b
  in
  let zeta_products:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_unpackhi_epi64 a b
  in
  let zetas:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 zeta_b3
      zeta_b2
      zeta_a3
      zeta_a2
      zeta_b1
      zeta_b0
      zeta_a1
      zeta_a0
  in
  let zeta_products:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply zeta_products zetas
  in
  let sub_terms:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 summands zeta_products
  in
  let add_terms:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 summands zeta_products
  in
  let a_terms_shuffled:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_unpacklo_epi64 add_terms sub_terms
  in
  let b_terms_shuffled:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_unpackhi_epi64 add_terms sub_terms
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      index
      ({
          Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
          =
          Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 (mk_i32 216) a_terms_shuffled
          <:
          Libcrux_intrinsics.Avx2_extract.t_Vec256
        }
        <:
        Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (index +! mk_usize 1 <: usize)
      ({
          Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
          =
          Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 (mk_i32 216) b_terms_shuffled
          <:
          Libcrux_intrinsics.Avx2_extract.t_Vec256
        }
        <:
        Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
  in
  re

let butterfly_4_
      (re: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      (index: usize)
      (zeta_a0 zeta_a1 zeta_b0 zeta_b1: i32)
     =
  let summands:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_unpacklo_epi64 (re.[ index ]
        <:
        Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
      (re.[ index +! mk_usize 1 <: usize ] <: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
  in
  let zeta_products:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_unpackhi_epi64 (re.[ index ]
        <:
        Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
      (re.[ index +! mk_usize 1 <: usize ] <: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
  in
  let zetas:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 zeta_b1
      zeta_b1
      zeta_a1
      zeta_a1
      zeta_b0
      zeta_b0
      zeta_a0
      zeta_a0
  in
  let zeta_products:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply zeta_products zetas
  in
  let sub_terms:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 summands zeta_products
  in
  let add_terms:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 summands zeta_products
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      index
      ({
          Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
          =
          Libcrux_intrinsics.Avx2_extract.mm256_unpacklo_epi64 add_terms sub_terms
          <:
          Libcrux_intrinsics.Avx2_extract.t_Vec256
        }
        <:
        Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (index +! mk_usize 1 <: usize)
      ({
          Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
          =
          Libcrux_intrinsics.Avx2_extract.mm256_unpackhi_epi64 add_terms sub_terms
          <:
          Libcrux_intrinsics.Avx2_extract.t_Vec256
        }
        <:
        Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
  in
  re

let butterfly_8_
      (re: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      (index: usize)
      (zeta0 zeta1: i32)
     =
  let summands:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_m128i (Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128
          (re.[ index +! mk_usize 1 <: usize ] <: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
            .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec128)
      (Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 (re.[ index ]
            <:
            Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
            .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec128)
  in
  let zeta_products:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_permute2x128_si256 (mk_i32 19)
      (re.[ index +! mk_usize 1 <: usize ] <: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
      (re.[ index ] <: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
  in
  let zetas:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 zeta1 zeta1 zeta1 zeta1 zeta0 zeta0 zeta0 zeta0
  in
  let zeta_products:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply zeta_products zetas
  in
  let sub_terms:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 summands zeta_products
  in
  let add_terms:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 summands zeta_products
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      index
      ({
          Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
          =
          Libcrux_intrinsics.Avx2_extract.mm256_set_m128i (Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128
                sub_terms
              <:
              Libcrux_intrinsics.Avx2_extract.t_Vec128)
            (Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 add_terms
              <:
              Libcrux_intrinsics.Avx2_extract.t_Vec128)
          <:
          Libcrux_intrinsics.Avx2_extract.t_Vec256
        }
        <:
        Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (index +! mk_usize 1 <: usize)
      ({
          Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
          =
          Libcrux_intrinsics.Avx2_extract.mm256_permute2x128_si256 (mk_i32 19) sub_terms add_terms
          <:
          Libcrux_intrinsics.Avx2_extract.t_Vec256
        }
        <:
        Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
  in
  re

let ntt_at_layer_0_ (re: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32)) =
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_2_ re (mk_usize 0) (mk_i32 2091667) (mk_i32 3407706) (mk_i32 2316500) (mk_i32 3817976)
      (mk_i32 (-3342478)) (mk_i32 2244091) (mk_i32 (-2446433)) (mk_i32 (-3562462))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_2_ re (mk_usize 2) (mk_i32 266997) (mk_i32 2434439) (mk_i32 (-1235728))
      (mk_i32 3513181) (mk_i32 (-3520352)) (mk_i32 (-3759364)) (mk_i32 (-1197226))
      (mk_i32 (-3193378))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_2_ re (mk_usize 4) (mk_i32 900702) (mk_i32 1859098) (mk_i32 909542) (mk_i32 819034)
      (mk_i32 495491) (mk_i32 (-1613174)) (mk_i32 (-43260)) (mk_i32 (-522500))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_2_ re (mk_usize 6) (mk_i32 (-655327)) (mk_i32 (-3122442)) (mk_i32 2031748)
      (mk_i32 3207046) (mk_i32 (-3556995)) (mk_i32 (-525098)) (mk_i32 (-768622)) (mk_i32 (-3595838))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_2_ re (mk_usize 8) (mk_i32 342297) (mk_i32 286988) (mk_i32 (-2437823))
      (mk_i32 4108315) (mk_i32 3437287) (mk_i32 (-3342277)) (mk_i32 1735879) (mk_i32 203044)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_2_ re (mk_usize 10) (mk_i32 2842341) (mk_i32 2691481) (mk_i32 (-2590150))
      (mk_i32 1265009) (mk_i32 4055324) (mk_i32 1247620) (mk_i32 2486353) (mk_i32 1595974)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_2_ re (mk_usize 12) (mk_i32 (-3767016)) (mk_i32 1250494) (mk_i32 2635921)
      (mk_i32 (-3548272)) (mk_i32 (-2994039)) (mk_i32 1869119) (mk_i32 1903435) (mk_i32 (-1050970))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_2_ re (mk_usize 14) (mk_i32 (-1333058)) (mk_i32 1237275) (mk_i32 (-3318210))
      (mk_i32 (-1430225)) (mk_i32 (-451100)) (mk_i32 1312455) (mk_i32 3306115) (mk_i32 (-1962642))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_2_ re (mk_usize 16) (mk_i32 (-1279661)) (mk_i32 1917081) (mk_i32 (-2546312))
      (mk_i32 (-1374803)) (mk_i32 1500165) (mk_i32 777191) (mk_i32 2235880) (mk_i32 3406031)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_2_ re (mk_usize 18) (mk_i32 (-542412)) (mk_i32 (-2831860)) (mk_i32 (-1671176))
      (mk_i32 (-1846953)) (mk_i32 (-2584293)) (mk_i32 (-3724270)) (mk_i32 594136)
      (mk_i32 (-3776993))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_2_ re (mk_usize 20) (mk_i32 (-2013608)) (mk_i32 2432395) (mk_i32 2454455)
      (mk_i32 (-164721)) (mk_i32 1957272) (mk_i32 3369112) (mk_i32 185531) (mk_i32 (-1207385))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_2_ re (mk_usize 22) (mk_i32 (-3183426)) (mk_i32 162844) (mk_i32 1616392)
      (mk_i32 3014001) (mk_i32 810149) (mk_i32 1652634) (mk_i32 (-3694233)) (mk_i32 (-1799107))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_2_ re (mk_usize 24) (mk_i32 (-3038916)) (mk_i32 3523897) (mk_i32 3866901)
      (mk_i32 269760) (mk_i32 2213111) (mk_i32 (-975884)) (mk_i32 1717735) (mk_i32 472078)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_2_ re (mk_usize 26) (mk_i32 (-426683)) (mk_i32 1723600) (mk_i32 (-1803090))
      (mk_i32 1910376) (mk_i32 (-1667432)) (mk_i32 (-1104333)) (mk_i32 (-260646))
      (mk_i32 (-3833893))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_2_ re (mk_usize 28) (mk_i32 (-2939036)) (mk_i32 (-2235985)) (mk_i32 (-420899))
      (mk_i32 (-2286327)) (mk_i32 183443) (mk_i32 (-976891)) (mk_i32 1612842) (mk_i32 (-3545687))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_2_ re (mk_usize 30) (mk_i32 (-554416)) (mk_i32 3919660) (mk_i32 (-48306))
      (mk_i32 (-1362209)) (mk_i32 3937738) (mk_i32 1400424) (mk_i32 (-846154)) (mk_i32 1976782)
  in
  re

let ntt_at_layer_1_ (re: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32)) =
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_4_ re
      (mk_usize 0)
      (mk_i32 (-3930395))
      (mk_i32 (-1528703))
      (mk_i32 (-3677745))
      (mk_i32 (-3041255))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_4_ re
      (mk_usize 2)
      (mk_i32 (-1452451))
      (mk_i32 3475950)
      (mk_i32 2176455)
      (mk_i32 (-1585221))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_4_ re
      (mk_usize 4)
      (mk_i32 (-1257611))
      (mk_i32 1939314)
      (mk_i32 (-4083598))
      (mk_i32 (-1000202))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_4_ re
      (mk_usize 6)
      (mk_i32 (-3190144))
      (mk_i32 (-3157330))
      (mk_i32 (-3632928))
      (mk_i32 126922)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_4_ re
      (mk_usize 8)
      (mk_i32 3412210)
      (mk_i32 (-983419))
      (mk_i32 2147896)
      (mk_i32 2715295)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_4_ re
      (mk_usize 10)
      (mk_i32 (-2967645))
      (mk_i32 (-3693493))
      (mk_i32 (-411027))
      (mk_i32 (-2477047))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_4_ re
      (mk_usize 12)
      (mk_i32 (-671102))
      (mk_i32 (-1228525))
      (mk_i32 (-22981))
      (mk_i32 (-1308169))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_4_ re
      (mk_usize 14)
      (mk_i32 (-381987))
      (mk_i32 1349076)
      (mk_i32 1852771)
      (mk_i32 (-1430430))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_4_ re
      (mk_usize 16)
      (mk_i32 (-3343383))
      (mk_i32 264944)
      (mk_i32 508951)
      (mk_i32 3097992)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_4_ re
      (mk_usize 18)
      (mk_i32 44288)
      (mk_i32 (-1100098))
      (mk_i32 904516)
      (mk_i32 3958618)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_4_ re
      (mk_usize 20)
      (mk_i32 (-3724342))
      (mk_i32 (-8578))
      (mk_i32 1653064)
      (mk_i32 (-3249728))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_4_ re
      (mk_usize 22)
      (mk_i32 2389356)
      (mk_i32 (-210977))
      (mk_i32 759969)
      (mk_i32 (-1316856))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_4_ re
      (mk_usize 24)
      (mk_i32 189548)
      (mk_i32 (-3553272))
      (mk_i32 3159746)
      (mk_i32 (-1851402))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_4_ re
      (mk_usize 26)
      (mk_i32 (-2409325))
      (mk_i32 (-177440))
      (mk_i32 1315589)
      (mk_i32 1341330)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_4_ re
      (mk_usize 28)
      (mk_i32 1285669)
      (mk_i32 (-1584928))
      (mk_i32 (-812732))
      (mk_i32 (-1439742))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_4_ re
      (mk_usize 30)
      (mk_i32 (-3019102))
      (mk_i32 (-3881060))
      (mk_i32 (-3628969))
      (mk_i32 3839961)
  in
  re

let ntt_at_layer_2_ (re: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32)) =
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_8_ re (mk_usize 0) (mk_i32 2706023) (mk_i32 95776)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_8_ re (mk_usize 2) (mk_i32 3077325) (mk_i32 3530437)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_8_ re (mk_usize 4) (mk_i32 (-1661693)) (mk_i32 (-3592148))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_8_ re (mk_usize 6) (mk_i32 (-2537516)) (mk_i32 3915439)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_8_ re (mk_usize 8) (mk_i32 (-3861115)) (mk_i32 (-3043716))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_8_ re (mk_usize 10) (mk_i32 3574422) (mk_i32 (-2867647))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_8_ re (mk_usize 12) (mk_i32 3539968) (mk_i32 (-300467))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_8_ re (mk_usize 14) (mk_i32 2348700) (mk_i32 (-539299))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_8_ re (mk_usize 16) (mk_i32 (-1699267)) (mk_i32 (-1643818))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_8_ re (mk_usize 18) (mk_i32 3505694) (mk_i32 (-3821735))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_8_ re (mk_usize 20) (mk_i32 3507263) (mk_i32 (-2140649))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_8_ re (mk_usize 22) (mk_i32 (-1600420)) (mk_i32 3699596)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_8_ re (mk_usize 24) (mk_i32 811944) (mk_i32 531354)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_8_ re (mk_usize 26) (mk_i32 954230) (mk_i32 3881043)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_8_ re (mk_usize 28) (mk_i32 3900724) (mk_i32 (-2556880))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    butterfly_8_ re (mk_usize 30) (mk_i32 2071892) (mk_i32 (-2797779))
  in
  re

let ntt_at_layer_7_and_6_ (re: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32)) =
  let field_modulus:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
  in
  let inverse_of_modulus_mod_montgomery_r:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (cast (Libcrux_ml_dsa.Simd.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
            <:
            u64)
        <:
        i32)
  in
  let zeta7:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (mk_i32 25847)
  in
  let zeta60:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (mk_i32 (-2608894))
  in
  let zeta61:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (mk_i32 (-518909))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_7_and_6___mul re
      (mk_usize 0)
      zeta7
      ntt_at_layer_7_and_6___STEP_BY_7_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_7_and_6___mul re
      (mk_usize 0 +! mk_usize 1 <: usize)
      zeta7
      ntt_at_layer_7_and_6___STEP_BY_7_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_7_and_6___mul re
      (mk_usize 0 +! mk_usize 2 <: usize)
      zeta7
      ntt_at_layer_7_and_6___STEP_BY_7_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_7_and_6___mul re
      (mk_usize 0 +! mk_usize 3 <: usize)
      zeta7
      ntt_at_layer_7_and_6___STEP_BY_7_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let _:Prims.unit = () in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_7_and_6___mul re
      (mk_usize 8)
      zeta7
      ntt_at_layer_7_and_6___STEP_BY_7_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_7_and_6___mul re
      (mk_usize 8 +! mk_usize 1 <: usize)
      zeta7
      ntt_at_layer_7_and_6___STEP_BY_7_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_7_and_6___mul re
      (mk_usize 8 +! mk_usize 2 <: usize)
      zeta7
      ntt_at_layer_7_and_6___STEP_BY_7_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_7_and_6___mul re
      (mk_usize 8 +! mk_usize 3 <: usize)
      zeta7
      ntt_at_layer_7_and_6___STEP_BY_7_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let _:Prims.unit = () in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_7_and_6___mul re
      (mk_usize 0)
      zeta60
      ntt_at_layer_7_and_6___STEP_BY_6_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_7_and_6___mul re
      (mk_usize 0 +! mk_usize 1 <: usize)
      zeta60
      ntt_at_layer_7_and_6___STEP_BY_6_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_7_and_6___mul re
      (mk_usize 0 +! mk_usize 2 <: usize)
      zeta60
      ntt_at_layer_7_and_6___STEP_BY_6_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_7_and_6___mul re
      (mk_usize 0 +! mk_usize 3 <: usize)
      zeta60
      ntt_at_layer_7_and_6___STEP_BY_6_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let _:Prims.unit = () in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_7_and_6___mul re
      (mk_usize 16)
      zeta61
      ntt_at_layer_7_and_6___STEP_BY_6_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_7_and_6___mul re
      (mk_usize 16 +! mk_usize 1 <: usize)
      zeta61
      ntt_at_layer_7_and_6___STEP_BY_6_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_7_and_6___mul re
      (mk_usize 16 +! mk_usize 2 <: usize)
      zeta61
      ntt_at_layer_7_and_6___STEP_BY_6_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_7_and_6___mul re
      (mk_usize 16 +! mk_usize 3 <: usize)
      zeta61
      ntt_at_layer_7_and_6___STEP_BY_6_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let _:Prims.unit = () in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_7_and_6___mul re
      (mk_usize 4)
      zeta7
      ntt_at_layer_7_and_6___STEP_BY_7_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_7_and_6___mul re
      (mk_usize 4 +! mk_usize 1 <: usize)
      zeta7
      ntt_at_layer_7_and_6___STEP_BY_7_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_7_and_6___mul re
      (mk_usize 4 +! mk_usize 2 <: usize)
      zeta7
      ntt_at_layer_7_and_6___STEP_BY_7_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_7_and_6___mul re
      (mk_usize 4 +! mk_usize 3 <: usize)
      zeta7
      ntt_at_layer_7_and_6___STEP_BY_7_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let _:Prims.unit = () in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_7_and_6___mul re
      (mk_usize 12)
      zeta7
      ntt_at_layer_7_and_6___STEP_BY_7_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_7_and_6___mul re
      (mk_usize 12 +! mk_usize 1 <: usize)
      zeta7
      ntt_at_layer_7_and_6___STEP_BY_7_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_7_and_6___mul re
      (mk_usize 12 +! mk_usize 2 <: usize)
      zeta7
      ntt_at_layer_7_and_6___STEP_BY_7_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_7_and_6___mul re
      (mk_usize 12 +! mk_usize 3 <: usize)
      zeta7
      ntt_at_layer_7_and_6___STEP_BY_7_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let _:Prims.unit = () in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_7_and_6___mul re
      (mk_usize 4)
      zeta60
      ntt_at_layer_7_and_6___STEP_BY_6_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_7_and_6___mul re
      (mk_usize 4 +! mk_usize 1 <: usize)
      zeta60
      ntt_at_layer_7_and_6___STEP_BY_6_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_7_and_6___mul re
      (mk_usize 4 +! mk_usize 2 <: usize)
      zeta60
      ntt_at_layer_7_and_6___STEP_BY_6_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_7_and_6___mul re
      (mk_usize 4 +! mk_usize 3 <: usize)
      zeta60
      ntt_at_layer_7_and_6___STEP_BY_6_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let _:Prims.unit = () in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_7_and_6___mul re
      (mk_usize 20)
      zeta61
      ntt_at_layer_7_and_6___STEP_BY_6_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_7_and_6___mul re
      (mk_usize 20 +! mk_usize 1 <: usize)
      zeta61
      ntt_at_layer_7_and_6___STEP_BY_6_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_7_and_6___mul re
      (mk_usize 20 +! mk_usize 2 <: usize)
      zeta61
      ntt_at_layer_7_and_6___STEP_BY_6_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_7_and_6___mul re
      (mk_usize 20 +! mk_usize 3 <: usize)
      zeta61
      ntt_at_layer_7_and_6___STEP_BY_6_
      field_modulus
      inverse_of_modulus_mod_montgomery_r
  in
  let _:Prims.unit = () in
  re

let ntt_at_layer_5_to_3___round
      (v_STEP v_STEP_BY: usize)
      (re: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      (index: usize)
      (zeta: i32)
     =
  let rhs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 zeta
  in
  let offset:usize =
    ((index *! v_STEP <: usize) *! mk_usize 2 <: usize) /!
    Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    Rust_primitives.Hax.Folds.fold_range offset
      (offset +! v_STEP_BY <: usize)
      (fun re temp_1_ ->
          let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) = re in
          let _:usize = temp_1_ in
          true)
      re
      (fun re j ->
          let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) = re in
          let j:usize = j in
          let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
              (j +! v_STEP_BY <: usize)
              ({
                  (re.[ j +! v_STEP_BY <: usize ] <: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256) with
                  Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
                  =
                  Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply (re.[ j +! v_STEP_BY
                        <:
                        usize ]
                      <:
                      Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
                      .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
                    rhs
                  <:
                  Libcrux_intrinsics.Avx2_extract.t_Vec256
                }
                <:
                Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
          in
          let tmp:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
            Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 (re.[ j ]
                <:
                Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
                .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
              (re.[ j +! v_STEP_BY <: usize ] <: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
                .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
          in
          let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
              j
              ({
                  Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
                  =
                  Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 (re.[ j ]
                      <:
                      Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
                      .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
                    (re.[ j +! v_STEP_BY <: usize ] <: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256
                    )
                      .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
                  <:
                  Libcrux_intrinsics.Avx2_extract.t_Vec256
                }
                <:
                Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
          in
          let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
              (j +! v_STEP_BY <: usize)
              ({ Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value = tmp }
                <:
                Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
          in
          re)
  in
  re

let ntt_at_layer_5_to_3_ (re: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32)) =
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_5_to_3___round (mk_usize 32) (mk_usize 4) re (mk_usize 0) (mk_i32 237124)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_5_to_3___round (mk_usize 32) (mk_usize 4) re (mk_usize 1) (mk_i32 (-777960))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_5_to_3___round (mk_usize 32) (mk_usize 4) re (mk_usize 2) (mk_i32 (-876248))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_5_to_3___round (mk_usize 32) (mk_usize 4) re (mk_usize 3) (mk_i32 466468)
  in
  let _:Prims.unit = () in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_5_to_3___round (mk_usize 16) (mk_usize 2) re (mk_usize 0) (mk_i32 1826347)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_5_to_3___round (mk_usize 16) (mk_usize 2) re (mk_usize 1) (mk_i32 2353451)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_5_to_3___round (mk_usize 16) (mk_usize 2) re (mk_usize 2) (mk_i32 (-359251))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_5_to_3___round (mk_usize 16) (mk_usize 2) re (mk_usize 3) (mk_i32 (-2091905))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_5_to_3___round (mk_usize 16) (mk_usize 2) re (mk_usize 4) (mk_i32 3119733)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_5_to_3___round (mk_usize 16) (mk_usize 2) re (mk_usize 5) (mk_i32 (-2884855))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_5_to_3___round (mk_usize 16) (mk_usize 2) re (mk_usize 6) (mk_i32 3111497)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_5_to_3___round (mk_usize 16) (mk_usize 2) re (mk_usize 7) (mk_i32 2680103)
  in
  let _:Prims.unit = () in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_5_to_3___round (mk_usize 8) (mk_usize 1) re (mk_usize 0) (mk_i32 2725464)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_5_to_3___round (mk_usize 8) (mk_usize 1) re (mk_usize 1) (mk_i32 1024112)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_5_to_3___round (mk_usize 8) (mk_usize 1) re (mk_usize 2) (mk_i32 (-1079900))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_5_to_3___round (mk_usize 8) (mk_usize 1) re (mk_usize 3) (mk_i32 3585928)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_5_to_3___round (mk_usize 8) (mk_usize 1) re (mk_usize 4) (mk_i32 (-549488))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_5_to_3___round (mk_usize 8) (mk_usize 1) re (mk_usize 5) (mk_i32 (-1119584))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_5_to_3___round (mk_usize 8) (mk_usize 1) re (mk_usize 6) (mk_i32 2619752)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_5_to_3___round (mk_usize 8) (mk_usize 1) re (mk_usize 7) (mk_i32 (-2108549))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_5_to_3___round (mk_usize 8) (mk_usize 1) re (mk_usize 8) (mk_i32 (-2118186))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_5_to_3___round (mk_usize 8) (mk_usize 1) re (mk_usize 9) (mk_i32 (-3859737))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_5_to_3___round (mk_usize 8) (mk_usize 1) re (mk_usize 10) (mk_i32 (-1399561))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_5_to_3___round (mk_usize 8) (mk_usize 1) re (mk_usize 11) (mk_i32 (-3277672))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_5_to_3___round (mk_usize 8) (mk_usize 1) re (mk_usize 12) (mk_i32 1757237)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_5_to_3___round (mk_usize 8) (mk_usize 1) re (mk_usize 13) (mk_i32 (-19422))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_5_to_3___round (mk_usize 8) (mk_usize 1) re (mk_usize 14) (mk_i32 4010497)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_5_to_3___round (mk_usize 8) (mk_usize 1) re (mk_usize 15) (mk_i32 280005)
  in
  let _:Prims.unit = () in
  let _:Prims.unit = () <: Prims.unit in
  re

let ntt__avx2_ntt (re: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32)) =
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_7_and_6_ re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
    ntt_at_layer_5_to_3_ re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) = ntt_at_layer_2_ re in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) = ntt_at_layer_1_ re in
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) = ntt_at_layer_0_ re in
  re

let ntt (re: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32)) =
  let re:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) = ntt__avx2_ntt re in
  re
