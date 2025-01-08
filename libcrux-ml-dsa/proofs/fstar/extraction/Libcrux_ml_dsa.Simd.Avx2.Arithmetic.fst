module Libcrux_ml_dsa.Simd.Avx2.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let add (lhs rhs: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let hax_temp_output, lhs:(Prims.unit & Libcrux_intrinsics.Avx2_extract.t_Vec256) =
    (), Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 lhs rhs
    <:
    (Prims.unit & Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  lhs

let compute_hint
      (low high: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (gamma2: i32)
      (hint: Libcrux_intrinsics.Avx2_extract.t_Vec256)
     =
  let minus_gamma2:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (Core.Ops.Arith.Neg.neg gamma2 <: i32)
  in
  let gamma2:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 gamma2
  in
  let low_within_bound:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_cmpgt_epi32 (Libcrux_intrinsics.Avx2_extract.mm256_abs_epi32
          low
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
      gamma2
  in
  let low_equals_minus_gamma2:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_cmpeq_epi32 low minus_gamma2
  in
  let low_equals_minus_gamma2_and_high_is_nonzero:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sign_epi32 low_equals_minus_gamma2 high
  in
  let hint:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_or_si256 low_within_bound
      low_equals_minus_gamma2_and_high_is_nonzero
  in
  let hints_mask:i32 =
    Libcrux_intrinsics.Avx2_extract.mm256_movemask_ps (Libcrux_intrinsics.Avx2_extract.mm256_castsi256_ps
          hint
        <:
        u8)
  in
  let hint:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_and_si256 hint
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 1l
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let hax_temp_output:usize = cast (Core.Num.impl__i32__count_ones hints_mask <: u32) <: usize in
  hint, hax_temp_output <: (Libcrux_intrinsics.Avx2_extract.t_Vec256 & usize)

let infinity_norm_exceeds (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) (bound: i32) =
  let absolute_values:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_abs_epi32 simd_unit
  in
  let bound:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (bound -! 1l <: i32)
  in
  let compare_with_bound:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_cmpgt_epi32 absolute_values bound
  in
  let result:i32 =
    Libcrux_intrinsics.Avx2_extract.mm256_testz_si256 compare_with_bound compare_with_bound
  in
  result <>. 1l

let subtract (lhs rhs: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let hax_temp_output, lhs:(Prims.unit & Libcrux_intrinsics.Avx2_extract.t_Vec256) =
    (), Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 lhs rhs
    <:
    (Prims.unit & Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  lhs

let shift_left_then_reduce (v_SHIFT_BY: i32) (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let shifted:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_slli_epi32 v_SHIFT_BY simd_unit
  in
  let quotient:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 shifted
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (1l <<! 22l <: i32)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let quotient:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srai_epi32 23l quotient
  in
  let quotient_times_field_modulus:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi32 quotient
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let simd_unit:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 shifted quotient_times_field_modulus
  in
  simd_unit

let to_unsigned_representatives_ret (t: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let signs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srai_epi32 31l t
  in
  let conditional_add_field_modulus:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_and_si256 signs
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 t conditional_add_field_modulus

let to_unsigned_representatives (t: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let t:Libcrux_intrinsics.Avx2_extract.t_Vec256 = to_unsigned_representatives_ret t in
  t

let power2round (r0 r1: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let r0:Libcrux_intrinsics.Avx2_extract.t_Vec256 = to_unsigned_representatives r0 in
  let r1:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 r0
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 ((1l <<!
              (Libcrux_ml_dsa.Constants.v_BITS_IN_LOWER_PART_OF_T -! sz 1 <: usize)
              <:
              i32) -!
            1l
            <:
            i32)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let r1:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srai_epi32 13l r1
  in
  let tmp:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_slli_epi32 13l r1
  in
  let r0:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 r0 tmp
  in
  r0, r1 <: (Libcrux_intrinsics.Avx2_extract.t_Vec256 & Libcrux_intrinsics.Avx2_extract.t_Vec256)

let montgomery_multiply (lhs rhs: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
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
  let prod02:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mul_epi32 lhs rhs
  in
  let prod13:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mul_epi32 (Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32
          245l
          lhs
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 245l rhs
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
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 245l res02
  in
  let lhs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_blend_epi32 170l res02_shifted res13
  in
  lhs

let montgomery_multiply_by_constant (lhs: Libcrux_intrinsics.Avx2_extract.t_Vec256) (constant: i32) =
  let rhs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 constant
  in
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
  let prod02:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mul_epi32 lhs rhs
  in
  let prod13:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mul_epi32 (Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32
          245l
          lhs
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 245l rhs
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
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 245l res02
  in
  Libcrux_intrinsics.Avx2_extract.mm256_blend_epi32 170l res02_shifted res13

let decompose (gamma2: i32) (r r0 r1: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let r:Libcrux_intrinsics.Avx2_extract.t_Vec256 = to_unsigned_representatives_ret r in
  let ceil_of_r_by_128_:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 r
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 127l
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let ceil_of_r_by_128_:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srai_epi32 7l ceil_of_r_by_128_
  in
  let r1:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    match gamma2 <: i32 with
    | 95232l ->
      let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
        Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi32 ceil_of_r_by_128_
          (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 11275l
            <:
            Libcrux_intrinsics.Avx2_extract.t_Vec256)
      in
      let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
        Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 result
          (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (1l <<! 23l <: i32)
            <:
            Libcrux_intrinsics.Avx2_extract.t_Vec256)
      in
      let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
        Libcrux_intrinsics.Avx2_extract.mm256_srai_epi32 24l result
      in
      let mask:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
        Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32
              43l
            <:
            Libcrux_intrinsics.Avx2_extract.t_Vec256)
          result
      in
      let mask:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
        Libcrux_intrinsics.Avx2_extract.mm256_srai_epi32 31l mask
      in
      let not_result:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
        Libcrux_intrinsics.Avx2_extract.mm256_xor_si256 result mask
      in
      let r1:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
        Libcrux_intrinsics.Avx2_extract.mm256_and_si256 result not_result
      in
      r1
    | 261888l ->
      let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
        Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi32 ceil_of_r_by_128_
          (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 1025l
            <:
            Libcrux_intrinsics.Avx2_extract.t_Vec256)
      in
      let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
        Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 result
          (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (1l <<! 21l <: i32)
            <:
            Libcrux_intrinsics.Avx2_extract.t_Vec256)
      in
      let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
        Libcrux_intrinsics.Avx2_extract.mm256_srai_epi32 22l result
      in
      let r1:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
        Libcrux_intrinsics.Avx2_extract.mm256_and_si256 result
          (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 15l
            <:
            Libcrux_intrinsics.Avx2_extract.t_Vec256)
      in
      r1
    | _ -> r1
  in
  let alpha:i32 = gamma2 *! 2l in
  let r0_tmp:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi32 r1
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 alpha
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let r0_tmp:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 r r0_tmp
  in
  let field_modulus_halved:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 ((Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS -!
          1l
          <:
          i32) /!
        2l
        <:
        i32)
  in
  let mask:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 field_modulus_halved r0_tmp
  in
  let mask:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srai_epi32 31l mask
  in
  let field_modulus_and_mask:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_and_si256 mask
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let r0:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 r0_tmp field_modulus_and_mask
  in
  r0, r1 <: (Libcrux_intrinsics.Avx2_extract.t_Vec256 & Libcrux_intrinsics.Avx2_extract.t_Vec256)

let use_hint (gamma2: i32) (r hint: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let r0, r1:(Libcrux_intrinsics.Avx2_extract.t_Vec256 & Libcrux_intrinsics.Avx2_extract.t_Vec256) =
    Libcrux_intrinsics.Avx2_extract.mm256_setzero_si256 (),
    Libcrux_intrinsics.Avx2_extract.mm256_setzero_si256 ()
    <:
    (Libcrux_intrinsics.Avx2_extract.t_Vec256 & Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let tmp0, tmp1:(Libcrux_intrinsics.Avx2_extract.t_Vec256 &
    Libcrux_intrinsics.Avx2_extract.t_Vec256) =
    decompose gamma2 r r0 r1
  in
  let r0:Libcrux_intrinsics.Avx2_extract.t_Vec256 = tmp0 in
  let r1:Libcrux_intrinsics.Avx2_extract.t_Vec256 = tmp1 in
  let _:Prims.unit = () in
  let all_zeros:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_setzero_si256 ()
  in
  let negate_hints:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.vec256_blendv_epi32 all_zeros hint r0
  in
  let negate_hints:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_slli_epi32 1l negate_hints
  in
  let hints:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 hint negate_hints
  in
  let r1_plus_hints:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 r1 hints
  in
  let (hint, r1_plus_hints), hax_temp_output:((Libcrux_intrinsics.Avx2_extract.t_Vec256 &
      Libcrux_intrinsics.Avx2_extract.t_Vec256) &
    Prims.unit) =
    match gamma2 <: i32 with
    | 95232l ->
      let max:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
        Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 43l
      in
      let r1_plus_hints:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
        Libcrux_intrinsics.Avx2_extract.vec256_blendv_epi32 r1_plus_hints max r1_plus_hints
      in
      let greater_than_or_equal_to_max:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
        Libcrux_intrinsics.Avx2_extract.mm256_cmpgt_epi32 r1_plus_hints max
      in
      let hint:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
        Libcrux_intrinsics.Avx2_extract.vec256_blendv_epi32 r1_plus_hints
          all_zeros
          greater_than_or_equal_to_max
      in
      (hint, r1_plus_hints
        <:
        (Libcrux_intrinsics.Avx2_extract.t_Vec256 & Libcrux_intrinsics.Avx2_extract.t_Vec256)),
      ()
      <:
      ((Libcrux_intrinsics.Avx2_extract.t_Vec256 & Libcrux_intrinsics.Avx2_extract.t_Vec256) &
        Prims.unit)
    | 261888l ->
      let hint:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
        Libcrux_intrinsics.Avx2_extract.mm256_and_si256 r1_plus_hints
          (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 15l
            <:
            Libcrux_intrinsics.Avx2_extract.t_Vec256)
      in
      (hint, r1_plus_hints
        <:
        (Libcrux_intrinsics.Avx2_extract.t_Vec256 & Libcrux_intrinsics.Avx2_extract.t_Vec256)),
      ()
      <:
      ((Libcrux_intrinsics.Avx2_extract.t_Vec256 & Libcrux_intrinsics.Avx2_extract.t_Vec256) &
        Prims.unit)
    | _ ->
      (hint, r1_plus_hints
        <:
        (Libcrux_intrinsics.Avx2_extract.t_Vec256 & Libcrux_intrinsics.Avx2_extract.t_Vec256)),
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

          <:
          Rust_primitives.Hax.t_Never)
      <:
      ((Libcrux_intrinsics.Avx2_extract.t_Vec256 & Libcrux_intrinsics.Avx2_extract.t_Vec256) &
        Prims.unit)
  in
  hint
