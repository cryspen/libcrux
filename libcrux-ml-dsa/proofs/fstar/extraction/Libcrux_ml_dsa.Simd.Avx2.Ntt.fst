module Libcrux_ml_dsa.Simd.Avx2.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let butterfly_2_
      (a b: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (zeta_a0 zeta_a1 zeta_a2 zeta_a3 zeta_b0 zeta_b1 zeta_b2 zeta_b3: i32)
     =
  let a_shuffled:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 216l a
  in
  let b_shuffled:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 216l b
  in
  let summands:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_unpacklo_epi64 a_shuffled b_shuffled
  in
  let zeta_multiplicands:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_unpackhi_epi64 a_shuffled b_shuffled
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
    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply zeta_multiplicands zetas
  in
  let add_terms:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.add summands zeta_products
  in
  let sub_terms:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.subtract summands zeta_products
  in
  let a_terms_shuffled:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_unpacklo_epi64 add_terms sub_terms
  in
  let b_terms_shuffled:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_unpackhi_epi64 add_terms sub_terms
  in
  let a_out:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 216l a_terms_shuffled
  in
  let b_out:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 216l b_terms_shuffled
  in
  a_out, b_out
  <:
  (Libcrux_intrinsics.Avx2_extract.t_Vec256 & Libcrux_intrinsics.Avx2_extract.t_Vec256)

let butterfly_4_
      (a b: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (zeta_a0 zeta_a1 zeta_b0 zeta_b1: i32)
     =
  let summands:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_unpacklo_epi64 a b
  in
  let zeta_multiplicands:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_unpackhi_epi64 a b
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
    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply zeta_multiplicands zetas
  in
  let add_terms:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.add summands zeta_products
  in
  let sub_terms:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.subtract summands zeta_products
  in
  let a_out:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_unpacklo_epi64 add_terms sub_terms
  in
  let b_out:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_unpackhi_epi64 add_terms sub_terms
  in
  a_out, b_out
  <:
  (Libcrux_intrinsics.Avx2_extract.t_Vec256 & Libcrux_intrinsics.Avx2_extract.t_Vec256)

let butterfly_8_ (a b: Libcrux_intrinsics.Avx2_extract.t_Vec256) (zeta0 zeta1: i32) =
  let summands:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_m128i (Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128
          b
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec128)
      (Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 a
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec128)
  in
  let zeta_multiplicands:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_permute2x128_si256 19l b a
  in
  let zetas:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 zeta1 zeta1 zeta1 zeta1 zeta0 zeta0 zeta0 zeta0
  in
  let zeta_products:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply zeta_multiplicands zetas
  in
  let add_terms:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.add summands zeta_products
  in
  let sub_terms:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.subtract summands zeta_products
  in
  let a_out:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_m128i (Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128
          sub_terms
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec128)
      (Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 add_terms
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec128)
  in
  let b_out:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_permute2x128_si256 19l sub_terms add_terms
  in
  a_out, b_out
  <:
  (Libcrux_intrinsics.Avx2_extract.t_Vec256 & Libcrux_intrinsics.Avx2_extract.t_Vec256)

let invert_ntt_at_layer_0_
      (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (zeta0 zeta1 zeta2 zeta3: i32)
     =
  let zetas:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 zeta3 0l zeta2 0l zeta1 0l zeta0 0l
  in
  let add_by_signs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (-1l) 1l (-1l) 1l (-1l) 1l (-1l) 1l
  in
  let add_by:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 177l simd_unit
  in
  let add_by:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi32 add_by add_by_signs
  in
  let sums:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 simd_unit add_by
  in
  let products:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply sums zetas
  in
  Libcrux_intrinsics.Avx2_extract.mm256_blend_epi32 170l sums products

let invert_ntt_at_layer_1_ (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) (zeta0 zeta1: i32) =
  let zetas:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 zeta1 zeta1 0l 0l zeta0 zeta0 0l 0l
  in
  let add_by_signs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (-1l) (-1l) 1l 1l (-1l) (-1l) 1l 1l
  in
  let add_by:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 78l simd_unit
  in
  let add_by:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi32 add_by add_by_signs
  in
  let sums:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 simd_unit add_by
  in
  let products:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply sums zetas
  in
  Libcrux_intrinsics.Avx2_extract.mm256_blend_epi32 204l sums products

let invert_ntt_at_layer_2_ (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) (zeta: i32) =
  let zetas:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 zeta zeta zeta zeta 0l 0l 0l 0l
  in
  let add_by_signs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (-1l) (-1l) (-1l) (-1l) 1l 1l 1l 1l
  in
  let add_by:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_permute4x64_epi64 78l simd_unit
  in
  let add_by:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi32 add_by add_by_signs
  in
  let sums:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 simd_unit add_by
  in
  let products:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply sums zetas
  in
  Libcrux_intrinsics.Avx2_extract.mm256_blend_epi32 240l sums products

let ntt_at_layer_3_plus
      (v_LAYER zeta_i: usize)
      (re: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
     =
  let step:usize = sz 1 <<! v_LAYER in
  let (re, zeta_i), hax_temp_output:(t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) &
    usize) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (sz 128 >>! v_LAYER <: usize)
      (fun temp_0_ temp_1_ ->
          let re, zeta_i:(t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) & usize) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (re, zeta_i <: (t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) & usize) =
            temp_0_
          in
          let round:usize = round in
          let zeta_i:usize = zeta_i +! sz 1 in
          let offset:usize =
            ((round *! step <: usize) *! sz 2 <: usize) /!
            Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT
          in
          let step_by:usize = step /! Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT in
          let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
            Rust_primitives.Hax.Folds.fold_range offset
              (offset +! step_by <: usize)
              (fun re temp_1_ ->
                  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) = re in
                  let _:usize = temp_1_ in
                  true)
              re
              (fun re j ->
                  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) = re in
                  let j:usize = j in
                  let t:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
                    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply_by_constant (re.[ j +!
                          step_by
                          <:
                          usize ]
                        <:
                        Libcrux_intrinsics.Avx2_extract.t_Vec256)
                      (Libcrux_ml_dsa.Simd.Traits.v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i ] <: i32)
                  in
                  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                      (j +! step_by <: usize)
                      (Libcrux_ml_dsa.Simd.Avx2.Arithmetic.subtract (re.[ j ]
                            <:
                            Libcrux_intrinsics.Avx2_extract.t_Vec256)
                          t
                        <:
                        Libcrux_intrinsics.Avx2_extract.t_Vec256)
                  in
                  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                      j
                      (Libcrux_ml_dsa.Simd.Avx2.Arithmetic.add (re.[ j ]
                            <:
                            Libcrux_intrinsics.Avx2_extract.t_Vec256)
                          t
                        <:
                        Libcrux_intrinsics.Avx2_extract.t_Vec256)
                  in
                  re)
          in
          re, zeta_i <: (t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) & usize))
  in
  zeta_i, re <: (usize & t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))

let ntt_at_layer_0_ (zeta_i: usize) (re: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32)) =
  let zeta_i:usize = zeta_i +! sz 1 in
  let re, zeta_i:(t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) & usize) =
    Rust_primitives.Hax.Folds.fold_range_step_by (sz 0)
      (Core.Slice.impl__len #Libcrux_intrinsics.Avx2_extract.t_Vec256
          (re <: t_Slice Libcrux_intrinsics.Avx2_extract.t_Vec256)
        <:
        usize)
      (sz 2)
      (fun temp_0_ temp_1_ ->
          let re, zeta_i:(t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) & usize) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (re, zeta_i <: (t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) & usize) =
            temp_0_
          in
          let round:usize = round in
          let a, b:(Libcrux_intrinsics.Avx2_extract.t_Vec256 &
            Libcrux_intrinsics.Avx2_extract.t_Vec256) =
            butterfly_2_ (re.[ round ] <: Libcrux_intrinsics.Avx2_extract.t_Vec256)
              (re.[ round +! sz 1 <: usize ] <: Libcrux_intrinsics.Avx2_extract.t_Vec256)
              (Libcrux_ml_dsa.Simd.Traits.v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i ] <: i32)
              (Libcrux_ml_dsa.Simd.Traits.v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i +! sz 1 <: usize ]
                <:
                i32)
              (Libcrux_ml_dsa.Simd.Traits.v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i +! sz 2 <: usize ]
                <:
                i32)
              (Libcrux_ml_dsa.Simd.Traits.v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i +! sz 3 <: usize ]
                <:
                i32)
              (Libcrux_ml_dsa.Simd.Traits.v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i +! sz 4 <: usize ]
                <:
                i32)
              (Libcrux_ml_dsa.Simd.Traits.v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i +! sz 5 <: usize ]
                <:
                i32)
              (Libcrux_ml_dsa.Simd.Traits.v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i +! sz 6 <: usize ]
                <:
                i32)
              (Libcrux_ml_dsa.Simd.Traits.v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i +! sz 7 <: usize ]
                <:
                i32)
          in
          let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re round a
          in
          let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
              (round +! sz 1 <: usize)
              b
          in
          let zeta_i:usize = zeta_i +! sz 8 in
          re, zeta_i <: (t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) & usize))
  in
  let zeta_i:usize = zeta_i -! sz 1 in
  zeta_i, re <: (usize & t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))

let ntt_at_layer_1_ (zeta_i: usize) (re: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32)) =
  let zeta_i:usize = zeta_i +! sz 1 in
  let re, zeta_i:(t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) & usize) =
    Rust_primitives.Hax.Folds.fold_range_step_by (sz 0)
      (Core.Slice.impl__len #Libcrux_intrinsics.Avx2_extract.t_Vec256
          (re <: t_Slice Libcrux_intrinsics.Avx2_extract.t_Vec256)
        <:
        usize)
      (sz 2)
      (fun temp_0_ temp_1_ ->
          let re, zeta_i:(t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) & usize) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (re, zeta_i <: (t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) & usize) =
            temp_0_
          in
          let round:usize = round in
          let a, b:(Libcrux_intrinsics.Avx2_extract.t_Vec256 &
            Libcrux_intrinsics.Avx2_extract.t_Vec256) =
            butterfly_4_ (re.[ round ] <: Libcrux_intrinsics.Avx2_extract.t_Vec256)
              (re.[ round +! sz 1 <: usize ] <: Libcrux_intrinsics.Avx2_extract.t_Vec256)
              (Libcrux_ml_dsa.Simd.Traits.v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i ] <: i32)
              (Libcrux_ml_dsa.Simd.Traits.v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i +! sz 1 <: usize ]
                <:
                i32)
              (Libcrux_ml_dsa.Simd.Traits.v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i +! sz 2 <: usize ]
                <:
                i32)
              (Libcrux_ml_dsa.Simd.Traits.v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i +! sz 3 <: usize ]
                <:
                i32)
          in
          let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re round a
          in
          let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
              (round +! sz 1 <: usize)
              b
          in
          let zeta_i:usize = zeta_i +! sz 4 in
          re, zeta_i <: (t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) & usize))
  in
  let zeta_i:usize = zeta_i -! sz 1 in
  zeta_i, re <: (usize & t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))

let ntt_at_layer_2_ (zeta_i: usize) (re: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32)) =
  let (re, zeta_i), hax_temp_output:(t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) &
    usize) =
    Rust_primitives.Hax.Folds.fold_range_step_by (sz 0)
      (Core.Slice.impl__len #Libcrux_intrinsics.Avx2_extract.t_Vec256
          (re <: t_Slice Libcrux_intrinsics.Avx2_extract.t_Vec256)
        <:
        usize)
      (sz 2)
      (fun temp_0_ temp_1_ ->
          let re, zeta_i:(t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) & usize) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (re, zeta_i <: (t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) & usize) =
            temp_0_
          in
          let round:usize = round in
          let zeta_i:usize = zeta_i +! sz 1 in
          let a, b:(Libcrux_intrinsics.Avx2_extract.t_Vec256 &
            Libcrux_intrinsics.Avx2_extract.t_Vec256) =
            butterfly_8_ (re.[ round ] <: Libcrux_intrinsics.Avx2_extract.t_Vec256)
              (re.[ round +! sz 1 <: usize ] <: Libcrux_intrinsics.Avx2_extract.t_Vec256)
              (Libcrux_ml_dsa.Simd.Traits.v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i ] <: i32)
              (Libcrux_ml_dsa.Simd.Traits.v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i +! sz 1 <: usize ]
                <:
                i32)
          in
          let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re round a
          in
          let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
              (round +! sz 1 <: usize)
              b
          in
          let zeta_i:usize = zeta_i +! sz 1 in
          re, zeta_i <: (t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) & usize))
  in
  zeta_i, re <: (usize & t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))

let ntt (re: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32)) =
  let zeta_i:usize = sz 0 in
  let tmp0, tmp1:(usize & t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32)) =
    ntt_at_layer_3_plus (sz 7) zeta_i re
  in
  let zeta_i:usize = tmp0 in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32)) =
    ntt_at_layer_3_plus (sz 6) zeta_i re
  in
  let zeta_i:usize = tmp0 in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32)) =
    ntt_at_layer_3_plus (sz 5) zeta_i re
  in
  let zeta_i:usize = tmp0 in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32)) =
    ntt_at_layer_3_plus (sz 4) zeta_i re
  in
  let zeta_i:usize = tmp0 in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32)) =
    ntt_at_layer_3_plus (sz 3) zeta_i re
  in
  let zeta_i:usize = tmp0 in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32)) =
    ntt_at_layer_2_ zeta_i re
  in
  let zeta_i:usize = tmp0 in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32)) =
    ntt_at_layer_1_ zeta_i re
  in
  let zeta_i:usize = tmp0 in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32)) =
    ntt_at_layer_0_ zeta_i re
  in
  let zeta_i:usize = tmp0 in
  let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) = tmp1 in
  let _:Prims.unit = () in
  re
