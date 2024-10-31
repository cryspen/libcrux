module Libcrux_ml_dsa.Simd.Avx2.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let add (lhs rhs: u8) = Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 lhs rhs

let compute_hint (v_GAMMA2: i32) (low high: u8) =
  let gamma2:u8 = Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 v_GAMMA2 in
  let minus_gamma2:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (Core.Ops.Arith.Neg.neg v_GAMMA2 <: i32)
  in
  let low_within_bound:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_cmpgt_epi32 (Libcrux_intrinsics.Avx2_extract.mm256_abs_epi32
          low
        <:
        u8)
      gamma2
  in
  let low_equals_minus_gamma2:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_cmpeq_epi32 low minus_gamma2
  in
  let low_equals_minus_gamma2_and_high_is_nonzero:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_sign_epi32 low_equals_minus_gamma2 high
  in
  let hints:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_or_si256 low_within_bound
      low_equals_minus_gamma2_and_high_is_nonzero
  in
  let hints_mask:i32 =
    Libcrux_intrinsics.Avx2_extract.mm256_movemask_ps (Libcrux_intrinsics.Avx2_extract.mm256_castsi256_ps
          hints
        <:
        u8)
  in
  (cast (Core.Num.impl__i32__count_ones hints_mask <: u32) <: usize),
  Libcrux_intrinsics.Avx2_extract.mm256_and_si256 hints
    (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 1l <: u8)
  <:
  (usize & u8)

let infinity_norm_exceeds (simd_unit: u8) (bound: i32) =
  let absolute_values:u8 = Libcrux_intrinsics.Avx2_extract.mm256_abs_epi32 simd_unit in
  let bound:u8 = Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (bound -! 1l <: i32) in
  let compare_with_bound:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_cmpgt_epi32 absolute_values bound
  in
  let result:i32 =
    Libcrux_intrinsics.Avx2_extract.mm256_testz_si256 compare_with_bound compare_with_bound
  in
  if result =. 1l then false else true

let subtract (lhs rhs: u8) = Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 lhs rhs

let shift_left_then_reduce (v_SHIFT_BY: i32) (simd_unit: u8) =
  let shifted:u8 = Libcrux_intrinsics.Avx2_extract.mm256_slli_epi32 v_SHIFT_BY simd_unit in
  let quotient:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 shifted
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (1l <<! 22l <: i32) <: u8)
  in
  let quotient:u8 = Libcrux_intrinsics.Avx2_extract.mm256_srai_epi32 23l quotient in
  let quotient_times_field_modulus:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi32 quotient
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
        <:
        u8)
  in
  Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 shifted quotient_times_field_modulus

let to_unsigned_representatives (t: u8) =
  let signs:u8 = Libcrux_intrinsics.Avx2_extract.mm256_srai_epi32 31l t in
  let conditional_add_field_modulus:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_and_si256 signs
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
        <:
        u8)
  in
  Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 t conditional_add_field_modulus

let power2round (r: u8) =
  let r:u8 = to_unsigned_representatives r in
  let r1:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 r
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 ((1l <<!
              (Libcrux_ml_dsa.Constants.v_BITS_IN_LOWER_PART_OF_T -! sz 1 <: usize)
              <:
              i32) -!
            1l
            <:
            i32)
        <:
        u8)
  in
  let r1:u8 = Libcrux_intrinsics.Avx2_extract.mm256_srai_epi32 13l r1 in
  let r0:u8 = Libcrux_intrinsics.Avx2_extract.mm256_slli_epi32 13l r1 in
  let r0:u8 = Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 r r0 in
  r0, r1 <: (u8 & u8)

let montgomery_multiply (lhs rhs: u8) =
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
  let prod02:u8 = Libcrux_intrinsics.Avx2_extract.mm256_mul_epi32 lhs rhs in
  let prod13:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_mul_epi32 (Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32
          245l
          lhs
        <:
        u8)
      (Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 245l rhs <: u8)
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
  Libcrux_intrinsics.Avx2_extract.mm256_blend_epi32 170l res02_shifted res13

let montgomery_multiply_by_constant (lhs: u8) (constant: i32) =
  let rhs:u8 = Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 constant in
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
  let prod02:u8 = Libcrux_intrinsics.Avx2_extract.mm256_mul_epi32 lhs rhs in
  let prod13:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_mul_epi32 (Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32
          245l
          lhs
        <:
        u8)
      (Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 245l rhs <: u8)
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
  Libcrux_intrinsics.Avx2_extract.mm256_blend_epi32 170l res02_shifted res13

let decompose (v_GAMMA2: i32) (r: u8) =
  let r:u8 = to_unsigned_representatives r in
  let field_modulus_halved:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 ((Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS -!
          1l
          <:
          i32) /!
        2l
        <:
        i32)
  in
  let (v_ALPHA: i32):i32 = v_GAMMA2 *! 2l in
  let ceil_of_r_by_128_:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 r
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 127l <: u8)
  in
  let ceil_of_r_by_128_:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_srai_epi32 7l ceil_of_r_by_128_
  in
  let r1:u8 =
    match v_ALPHA with
    | 190464l ->
      let result:u8 =
        Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi32 ceil_of_r_by_128_
          (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 11275l <: u8)
      in
      let result:u8 =
        Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 result
          (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (1l <<! 23l <: i32) <: u8)
      in
      let result:u8 = Libcrux_intrinsics.Avx2_extract.mm256_srai_epi32 24l result in
      let mask:u8 =
        Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32
              43l
            <:
            u8)
          result
      in
      let mask:u8 = Libcrux_intrinsics.Avx2_extract.mm256_srai_epi32 31l mask in
      let not_result:u8 = Libcrux_intrinsics.Avx2_extract.mm256_xor_si256 result mask in
      Libcrux_intrinsics.Avx2_extract.mm256_and_si256 result not_result
    | 523776l ->
      let result:u8 =
        Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi32 ceil_of_r_by_128_
          (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 1025l <: u8)
      in
      let result:u8 =
        Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 result
          (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (1l <<! 21l <: i32) <: u8)
      in
      let result:u8 = Libcrux_intrinsics.Avx2_extract.mm256_srai_epi32 22l result in
      Libcrux_intrinsics.Avx2_extract.mm256_and_si256 result
        (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 15l <: u8)
    | _ ->
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

          <:
          Rust_primitives.Hax.t_Never)
  in
  let r0:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi32 r1
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 v_ALPHA <: u8)
  in
  let r0:u8 = Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 r r0 in
  let mask:u8 = Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 field_modulus_halved r0 in
  let mask:u8 = Libcrux_intrinsics.Avx2_extract.mm256_srai_epi32 31l mask in
  let field_modulus_and_mask:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_and_si256 mask
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
        <:
        u8)
  in
  let r0:u8 = Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 r0 field_modulus_and_mask in
  r0, r1 <: (u8 & u8)

let use_hint (v_GAMMA2: i32) (r hint: u8) =
  let r0, r1:(u8 & u8) = decompose v_GAMMA2 r in
  let all_zeros:u8 = Libcrux_intrinsics.Avx2_extract.mm256_setzero_si256 () in
  let negate_hints:u8 = Libcrux_intrinsics.Avx2_extract.vec256_blendv_epi32 all_zeros hint r0 in
  let negate_hints:u8 = Libcrux_intrinsics.Avx2_extract.mm256_slli_epi32 1l negate_hints in
  let hints:u8 = Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 hint negate_hints in
  let r1_plus_hints:u8 = Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 r1 hints in
  match v_GAMMA2 with
  | 95232l ->
    let max:u8 = Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 43l in
    let r1_plus_hints:u8 =
      Libcrux_intrinsics.Avx2_extract.vec256_blendv_epi32 r1_plus_hints max r1_plus_hints
    in
    let greater_than_or_equal_to_max:u8 =
      Libcrux_intrinsics.Avx2_extract.mm256_cmpgt_epi32 r1_plus_hints max
    in
    Libcrux_intrinsics.Avx2_extract.vec256_blendv_epi32 r1_plus_hints
      all_zeros
      greater_than_or_equal_to_max
  | 261888l ->
    Libcrux_intrinsics.Avx2_extract.mm256_and_si256 r1_plus_hints
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 15l <: u8)
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)
