module Libcrux_ml_dsa.Simd.Avx2.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let to_unsigned_representatives_ret (t: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)) =
  let signs:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_srai_epi32 (mk_i32 31) t
  in
  let conditional_add_field_modulus:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_and_si256 signs
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
        <:
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 t conditional_add_field_modulus

let to_unsigned_representatives (t: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)) =
  let t:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) = to_unsigned_representatives_ret t in
  t

let add (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)) =
  let lhs:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 lhs rhs
  in
  lhs

let subtract (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)) =
  let lhs:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 lhs rhs
  in
  lhs

let montgomery_multiply_by_constant
      (lhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (constant: i32)
     =
  let rhs:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 constant
  in
  let field_modulus:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
  in
  let inverse_of_modulus_mod_montgomery_r:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (cast (Libcrux_ml_dsa.Simd.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
            <:
            u64)
        <:
        i32)
  in
  let prod02:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_mul_epi32 lhs rhs
  in
  let prod13:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_mul_epi32 (Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32
          (mk_i32 245)
          lhs
        <:
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 (mk_i32 245) rhs
        <:
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let k02:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_mul_epi32 prod02 inverse_of_modulus_mod_montgomery_r
  in
  let k13:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_mul_epi32 prod13 inverse_of_modulus_mod_montgomery_r
  in
  let c02:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_mul_epi32 k02 field_modulus
  in
  let c13:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_mul_epi32 k13 field_modulus
  in
  let res02:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 prod02 c02
  in
  let res13:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 prod13 c13
  in
  let res02_shifted:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 (mk_i32 245) res02
  in
  Libcrux_intrinsics.Avx2_extract.mm256_blend_epi32 (mk_i32 170) res02_shifted res13

let montgomery_multiply (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)) =
  let field_modulus:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
  in
  let inverse_of_modulus_mod_montgomery_r:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (cast (Libcrux_ml_dsa.Simd.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
            <:
            u64)
        <:
        i32)
  in
  let prod02:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_mul_epi32 lhs rhs
  in
  let prod13:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_mul_epi32 (Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32
          (mk_i32 245)
          lhs
        <:
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 (mk_i32 245) rhs
        <:
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let k02:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_mul_epi32 prod02 inverse_of_modulus_mod_montgomery_r
  in
  let k13:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_mul_epi32 prod13 inverse_of_modulus_mod_montgomery_r
  in
  let c02:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_mul_epi32 k02 field_modulus
  in
  let c13:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_mul_epi32 k13 field_modulus
  in
  let res02:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 prod02 c02
  in
  let res13:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 prod13 c13
  in
  let res02_shifted:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 (mk_i32 245) res02
  in
  let lhs:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_blend_epi32 (mk_i32 170) res02_shifted res13
  in
  lhs

let shift_left_then_reduce
      (v_SHIFT_BY: i32)
      (simd_unit: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
     =
  let shifted:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_slli_epi32 v_SHIFT_BY simd_unit
  in
  let quotient:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 shifted
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (mk_i32 1 <<! mk_i32 22 <: i32)
        <:
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let quotient:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_srai_epi32 (mk_i32 23) quotient
  in
  let quotient_times_field_modulus:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi32 quotient
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
        <:
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let simd_unit:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 shifted quotient_times_field_modulus
  in
  simd_unit

let infinity_norm_exceeds
      (simd_unit: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (bound: i32)
     =
  let absolute_values:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_abs_epi32 simd_unit
  in
  let bound:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (bound -! mk_i32 1 <: i32)
  in
  let compare_with_bound:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_cmpgt_epi32 absolute_values bound
  in
  let result:i32 =
    Libcrux_intrinsics.Avx2_extract.mm256_testz_si256 compare_with_bound compare_with_bound
  in
  result <>. mk_i32 1

let power2round (r0 r1: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)) =
  let r0:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) = to_unsigned_representatives r0 in
  let r1:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 r0
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 ((mk_i32 1 <<!
              (Libcrux_ml_dsa.Constants.v_BITS_IN_LOWER_PART_OF_T -! mk_usize 1 <: usize)
              <:
              i32) -!
            mk_i32 1
            <:
            i32)
        <:
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let r1:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_srai_epi32 (mk_i32 13) r1
  in
  let tmp:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_slli_epi32 (mk_i32 13) r1
  in
  let r0:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 r0 tmp
  in
  r0, r1
  <:
  (Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) &
    Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))

let decompose (gamma2: i32) (r r0 r1: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)) =
  let r:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) = to_unsigned_representatives_ret r in
  let ceil_of_r_by_128_:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 r
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (mk_i32 127)
        <:
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let ceil_of_r_by_128_:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_srai_epi32 (mk_i32 7) ceil_of_r_by_128_
  in
  let r1:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    match gamma2 <: i32 with
    | Rust_primitives.Integers.MkInt 95232 ->
      let result:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi32 ceil_of_r_by_128_
          (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (mk_i32 11275)
            <:
            Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      in
      let result:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 result
          (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (mk_i32 1 <<! mk_i32 23 <: i32)
            <:
            Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      in
      let result:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2_extract.mm256_srai_epi32 (mk_i32 24) result
      in
      let mask:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32
              (mk_i32 43)
            <:
            Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
          result
      in
      let mask:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2_extract.mm256_srai_epi32 (mk_i32 31) mask
      in
      let not_result:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2_extract.mm256_xor_si256 result mask
      in
      let r1:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2_extract.mm256_and_si256 result not_result
      in
      r1
    | Rust_primitives.Integers.MkInt 261888 ->
      let result:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi32 ceil_of_r_by_128_
          (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (mk_i32 1025)
            <:
            Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      in
      let result:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 result
          (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (mk_i32 1 <<! mk_i32 21 <: i32)
            <:
            Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      in
      let result:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2_extract.mm256_srai_epi32 (mk_i32 22) result
      in
      let r1:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2_extract.mm256_and_si256 result
          (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (mk_i32 15)
            <:
            Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      in
      r1
    | _ -> r1
  in
  let alpha:i32 = gamma2 *! mk_i32 2 in
  let r0_tmp:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi32 r1
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 alpha
        <:
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let r0_tmp:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 r r0_tmp
  in
  let field_modulus_halved:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 ((Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS -!
          mk_i32 1
          <:
          i32) /!
        mk_i32 2
        <:
        i32)
  in
  let mask:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 field_modulus_halved r0_tmp
  in
  let mask:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_srai_epi32 (mk_i32 31) mask
  in
  let field_modulus_and_mask:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_and_si256 mask
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
        <:
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let r0:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 r0_tmp field_modulus_and_mask
  in
  r0, r1
  <:
  (Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) &
    Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))

let compute_hint
      (low high: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (gamma2: i32)
      (hint: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
     =
  let minus_gamma2:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (Core.Ops.Arith.f_neg gamma2 <: i32)
  in
  let gamma2:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 gamma2
  in
  let low_within_bound:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_cmpgt_epi32 (Libcrux_intrinsics.Avx2_extract.mm256_abs_epi32
          low
        <:
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      gamma2
  in
  let low_equals_minus_gamma2:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_cmpeq_epi32 low minus_gamma2
  in
  let low_equals_minus_gamma2_and_high_is_nonzero:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  =
    Libcrux_intrinsics.Avx2_extract.mm256_sign_epi32 low_equals_minus_gamma2 high
  in
  let hint:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_or_si256 low_within_bound
      low_equals_minus_gamma2_and_high_is_nonzero
  in
  let hints_mask:i32 =
    Libcrux_intrinsics.Avx2_extract.mm256_movemask_ps (Libcrux_intrinsics.Avx2_extract.mm256_castsi256_ps
          hint
        <:
        u8)
  in
  let hint:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_and_si256 hint
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (mk_i32 1)
        <:
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let hax_temp_output:usize = cast (Core.Num.impl_i32__count_ones hints_mask <: u32) <: usize in
  hint, hax_temp_output <: (Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) & usize)

let uuse_hint (gamma2: i32) (r hint: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)) =
  let r0, r1:(Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) &
    Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)) =
    Libcrux_intrinsics.Avx2_extract.mm256_setzero_si256 (),
    Libcrux_intrinsics.Avx2_extract.mm256_setzero_si256 ()
    <:
    (Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) &
      Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let tmp0, tmp1:(Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) &
    Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)) =
    decompose gamma2 r r0 r1
  in
  let r0:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) = tmp0 in
  let r1:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) = tmp1 in
  let _:Prims.unit = () in
  let all_zeros:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_setzero_si256 ()
  in
  let negate_hints:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.vec256_blendv_epi32 all_zeros hint r0
  in
  let negate_hints:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_slli_epi32 (mk_i32 1) negate_hints
  in
  let hints:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi32 hint negate_hints
  in
  let r1_plus_hints:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 r1 hints
  in
  let hint, r1_plus_hints:(Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) &
    Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)) =
    match gamma2 <: i32 with
    | Rust_primitives.Integers.MkInt 95232 ->
      let max:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (mk_i32 43)
      in
      let r1_plus_hints:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2_extract.vec256_blendv_epi32 r1_plus_hints max r1_plus_hints
      in
      let greater_than_or_equal_to_max:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2_extract.mm256_cmpgt_epi32 r1_plus_hints max
      in
      let hint:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2_extract.vec256_blendv_epi32 r1_plus_hints
          all_zeros
          greater_than_or_equal_to_max
      in
      hint, r1_plus_hints
      <:
      (Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) &
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    | Rust_primitives.Integers.MkInt 261888 ->
      let hint:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2_extract.mm256_and_si256 r1_plus_hints
          (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (mk_i32 15)
            <:
            Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      in
      hint, r1_plus_hints
      <:
      (Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) &
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    | _ ->
      hint, r1_plus_hints
      <:
      (Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) &
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  hint
