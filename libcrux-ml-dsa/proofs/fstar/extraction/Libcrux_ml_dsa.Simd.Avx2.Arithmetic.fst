module Libcrux_ml_dsa.Simd.Avx2.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let to_unsigned_representatives_ret (t: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let signs:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_srai_epi32 (mk_i32 31) t
  in
  let conditional_add_field_modulus:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_and_si256 signs
      (Libcrux_intrinsics.Avx2.mm256_set1_epi32 Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  Libcrux_intrinsics.Avx2.mm256_add_epi32 t conditional_add_field_modulus

let to_unsigned_representatives (t: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let t:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) = to_unsigned_representatives_ret t in
  t

let add (lhs rhs: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let lhs:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_add_epi32 lhs rhs
  in
  lhs

let subtract (lhs rhs: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let lhs:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_sub_epi32 lhs rhs
  in
  lhs

let montgomery_multiply_by_constant
      (lhs: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (constant: i32)
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let rhs:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_set1_epi32 constant
  in
  let field_modulus:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_set1_epi32 Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
  in
  let inverse_of_modulus_mod_montgomery_r:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_set1_epi32 (cast (Libcrux_ml_dsa.Simd.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
            <:
            u64)
        <:
        i32)
  in
  let prod02:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_mul_epi32 lhs rhs
  in
  let prod13:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_mul_epi32 (Libcrux_intrinsics.Avx2.mm256_shuffle_epi32 (mk_i32 245
          )
          lhs
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (Libcrux_intrinsics.Avx2.mm256_shuffle_epi32 (mk_i32 245) rhs
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let k02:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_mul_epi32 prod02 inverse_of_modulus_mod_montgomery_r
  in
  let k13:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_mul_epi32 prod13 inverse_of_modulus_mod_montgomery_r
  in
  let c02:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_mul_epi32 k02 field_modulus
  in
  let c13:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_mul_epi32 k13 field_modulus
  in
  let res02:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_sub_epi32 prod02 c02
  in
  let res13:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_sub_epi32 prod13 c13
  in
  let res02_shifted:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_shuffle_epi32 (mk_i32 245) res02
  in
  Libcrux_intrinsics.Avx2.mm256_blend_epi32 (mk_i32 170) res02_shifted res13

unfold let montgomery_multiply_spec__i32_extended64_mul (x y: i32) : i64 =
  (cast (x <: i32) <: i64) *! (cast (y <: i32) <: i64)

let montgomery_multiply_spec (x y: i32) : i32 =
  let x_mul_y:i64 = montgomery_multiply_spec__i32_extended64_mul x y in
  let lhs:i32 = cast (x_mul_y >>! mk_i32 32 <: i64) <: i32 in
  let rhs:i32 =
    cast (((cast (cast (montgomery_multiply_spec__i32_extended64_mul (cast (x_mul_y <: i64) <: i32)
                      (cast (Libcrux_ml_dsa.Simd.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R <: u64
                          )
                        <:
                        i32)
                    <:
                    i64)
                <:
                i32)
            <:
            i64) *!
          (cast (Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS <: i32) <: i64)
          <:
          i64) >>!
        mk_i32 32
        <:
        i64)
    <:
    i32
  in
  Core.Num.impl_i32__wrapping_sub lhs rhs

let montgomery_multiply_spec_rw (x y: i32) : Lemma ((let x_mul_y:i64 = montgomery_multiply_spec__i32_extended64_mul x y in
  let lhs:i32 = cast (x_mul_y >>! mk_i32 32 <: i64) <: i32 in
  let rhs:i32 =
    cast (((cast (cast (montgomery_multiply_spec__i32_extended64_mul (cast (x_mul_y <: i64) <: i32)
                      (cast (Libcrux_ml_dsa.Simd.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R <: u64
                          )
                        <:
                        i32)
                    <:
                    i64)
                <:
                i32)
            <:
            i64) *!
          (cast (Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS <: i32) <: i64)
          <:
          i64) >>!
        mk_i32 32
        <:
        i64)
    <:
    i32
  in
  Core.Num.impl_i32__wrapping_sub lhs rhs) == montgomery_multiply_spec x y)
  = ()

[@@FStar.Tactics.postprocess_with ( fun _ -> 
  let open Tactics.Circuits in
  let open FStar.Tactics in
  let open Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas in
  flatten_circuit_aux
      [
          "Core_models";
          "FStar.FunctionalExtensionality";
          `%Rust_primitives.cast_tc; `%Rust_primitives.unsize_tc;
          "Core.Ops"; `%(.[]);
          `%Core_models.Abstractions.Bitvec.Int_vec_interp.impl__into_i32x8;
          `%Core_models.Abstractions.Bitvec.Int_vec_interp.impl_1__into_i64x4;
      ]
      (top_levels_of_attr (` v_LIFT_LEMMA ))
      (top_levels_of_attr (` Core_models.Abstractions.Bitvec.Int_vec_interp.v_SIMPLIFICATION_LEMMA ))
      (top_levels_of_attr (` v_ETA_MATCH_EXPAND ))
      (mk_dbg "");
  dump "AAAA";
  l_to_r [`montgomery_multiply_spec_rw];
  trefl ();
  ()
  // Core_models.Core_arch.X86.……¬…Interpretations.Int_vec.Lemmas.flatten_circuit
)]

let montgomery_multiply (lhs rhs: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let field_modulus:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_set1_epi32 Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
  in
  let inverse_of_modulus_mod_montgomery_r:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_set1_epi32 (cast (Libcrux_ml_dsa.Simd.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
            <:
            u64)
        <:
        i32)
  in
  let prod02:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_mul_epi32 lhs rhs
  in
  let prod13:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_mul_epi32 (Libcrux_intrinsics.Avx2.mm256_shuffle_epi32 (mk_i32 245
          )
          lhs
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (Libcrux_intrinsics.Avx2.mm256_shuffle_epi32 (mk_i32 245) rhs
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let k02:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_mul_epi32 prod02 inverse_of_modulus_mod_montgomery_r
  in
  let k13:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_mul_epi32 prod13 inverse_of_modulus_mod_montgomery_r
  in
  let c02:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_mul_epi32 k02 field_modulus
  in
  let c13:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_mul_epi32 k13 field_modulus
  in
  let res02:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_sub_epi32 prod02 c02
  in
  let res13:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_sub_epi32 prod13 c13
  in
  let res02_shifted:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_shuffle_epi32 (mk_i32 245) res02
  in
  let lhs:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_blend_epi32 (mk_i32 170) res02_shifted res13
  in
  lhs

module BV_LEMMAS = Core_models.Abstractions.Bitvec.Int_vec_interp


///Lemma that asserts that applying BitVec :: < 256 > :: from and then i32x8 :: from is the identity.
let e_ee_1__lemma_cancel_iv'
  (x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32) 
  arg
  : Lemma
      (ensures
        (BV_LEMMAS.e_ee_1__impl__to_i32x8 (BV_LEMMAS.e_ee_1__impl__from_i32x8 x
              <:
              Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32) arg ==
        x arg)
      [
        SMTPat
        ((BV_LEMMAS.e_ee_1__impl__to_i32x8 (BV_LEMMAS.e_ee_1__impl__from_i32x8 x
              <:
              Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32) arg)
      ]
      = admit ()


let hey lhs rhs: squash (
        Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl__to_i32x8 (montgomery_multiply lhs rhs) (mk_u64 0)
     == montgomery_multiply_spec 
          (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl__to_i32x8 lhs (mk_u64 0)) 
          (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl__to_i32x8 rhs (mk_u64 0))
    ) = _ by (
      let open FStar.Tactics in
      norm [iota; primops; delta_only [`%montgomery_multiply]; zeta];
      l_to_r [`e_ee_1__lemma_cancel_iv'];
      dump "goal"
    )

let shift_left_then_reduce
      (v_SHIFT_BY: i32)
      (simd_unit: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let shifted:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_slli_epi32 v_SHIFT_BY simd_unit
  in
  let quotient:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_add_epi32 shifted
      (Libcrux_intrinsics.Avx2.mm256_set1_epi32 (mk_i32 1 <<! mk_i32 22 <: i32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let quotient:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_srai_epi32 (mk_i32 23) quotient
  in
  let quotient_times_field_modulus:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_mullo_epi32 quotient
      (Libcrux_intrinsics.Avx2.mm256_set1_epi32 Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let simd_unit:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_sub_epi32 shifted quotient_times_field_modulus
  in
  simd_unit

#push-options "--admit_smt_queries true"

let infinity_norm_exceeds
      (simd_unit: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (bound: i32)
    : bool =
  let absolute_values:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_abs_epi32 simd_unit
  in
  let bound:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_set1_epi32 (bound -! mk_i32 1 <: i32)
  in
  let compare_with_bound:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_cmpgt_epi32 absolute_values bound
  in
  let result:i32 =
    Libcrux_intrinsics.Avx2.mm256_testz_si256 compare_with_bound compare_with_bound
  in
  result <>. mk_i32 1

#pop-options

#push-options "--admit_smt_queries true"

let power2round (r0 r1: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) &
      Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) =
  let r0:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) = to_unsigned_representatives r0 in
  let r1:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_add_epi32 r0
      (Libcrux_intrinsics.Avx2.mm256_set1_epi32 ((mk_i32 1 <<!
              (Libcrux_ml_dsa.Constants.v_BITS_IN_LOWER_PART_OF_T -! mk_usize 1 <: usize)
              <:
              i32) -!
            mk_i32 1
            <:
            i32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let r1:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_srai_epi32 (mk_i32 13) r1
  in
  let tmp:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_slli_epi32 (mk_i32 13) r1
  in
  let r0:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_sub_epi32 r0 tmp
  in
  r0, r1
  <:
  (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) &
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))

#pop-options

#push-options "--admit_smt_queries true"

let decompose (gamma2: i32) (r r0 r1: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) &
      Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) =
  let r:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) = to_unsigned_representatives_ret r in
  let ceil_of_r_by_128_:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_add_epi32 r
      (Libcrux_intrinsics.Avx2.mm256_set1_epi32 (mk_i32 127)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let ceil_of_r_by_128_:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_srai_epi32 (mk_i32 7) ceil_of_r_by_128_
  in
  let r1:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    match gamma2 <: i32 with
    | Rust_primitives.Integers.MkInt 95232 ->
      let result:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2.mm256_mullo_epi32 ceil_of_r_by_128_
          (Libcrux_intrinsics.Avx2.mm256_set1_epi32 (mk_i32 11275)
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      in
      let result:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2.mm256_add_epi32 result
          (Libcrux_intrinsics.Avx2.mm256_set1_epi32 (mk_i32 1 <<! mk_i32 23 <: i32)
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      in
      let result:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2.mm256_srai_epi32 (mk_i32 24) result
      in
      let mask:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2.mm256_sub_epi32 (Libcrux_intrinsics.Avx2.mm256_set1_epi32 (mk_i32 43
              )
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
          result
      in
      let mask:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2.mm256_srai_epi32 (mk_i32 31) mask
      in
      let not_result:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2.mm256_xor_si256 result mask
      in
      let r1:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2.mm256_and_si256 result not_result
      in
      r1
    | Rust_primitives.Integers.MkInt 261888 ->
      let result:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2.mm256_mullo_epi32 ceil_of_r_by_128_
          (Libcrux_intrinsics.Avx2.mm256_set1_epi32 (mk_i32 1025)
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      in
      let result:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2.mm256_add_epi32 result
          (Libcrux_intrinsics.Avx2.mm256_set1_epi32 (mk_i32 1 <<! mk_i32 21 <: i32)
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      in
      let result:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2.mm256_srai_epi32 (mk_i32 22) result
      in
      let r1:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2.mm256_and_si256 result
          (Libcrux_intrinsics.Avx2.mm256_set1_epi32 (mk_i32 15)
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      in
      r1
    | _ -> r1
  in
  let alpha:i32 = gamma2 *! mk_i32 2 in
  let r0_tmp:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_mullo_epi32 r1
      (Libcrux_intrinsics.Avx2.mm256_set1_epi32 alpha
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let r0_tmp:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_sub_epi32 r r0_tmp
  in
  let field_modulus_halved:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_set1_epi32 ((Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS -!
          mk_i32 1
          <:
          i32) /!
        mk_i32 2
        <:
        i32)
  in
  let mask:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_sub_epi32 field_modulus_halved r0_tmp
  in
  let mask:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_srai_epi32 (mk_i32 31) mask
  in
  let field_modulus_and_mask:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_and_si256 mask
      (Libcrux_intrinsics.Avx2.mm256_set1_epi32 Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let r0:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_sub_epi32 r0_tmp field_modulus_and_mask
  in
  r0, r1
  <:
  (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) &
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))

#pop-options

#push-options "--admit_smt_queries true"

let compute_hint
      (low high: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (gamma2: i32)
      (hint: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) & usize) =
  let minus_gamma2:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_set1_epi32 (Core.Ops.Arith.f_neg gamma2 <: i32)
  in
  let gamma2:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_set1_epi32 gamma2
  in
  let low_within_bound:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_cmpgt_epi32 (Libcrux_intrinsics.Avx2.mm256_abs_epi32 low
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      gamma2
  in
  let low_equals_minus_gamma2:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_cmpeq_epi32 low minus_gamma2
  in
  let low_equals_minus_gamma2_and_high_is_nonzero:Core_models.Abstractions.Bitvec.t_BitVec
  (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_sign_epi32 low_equals_minus_gamma2 high
  in
  let hint:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_or_si256 low_within_bound
      low_equals_minus_gamma2_and_high_is_nonzero
  in
  let hints_mask:i32 =
    Libcrux_intrinsics.Avx2.mm256_movemask_ps (Libcrux_intrinsics.Avx2.mm256_castsi256_ps hint
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let hint:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_and_si256 hint
      (Libcrux_intrinsics.Avx2.mm256_set1_epi32 (mk_i32 1)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let hax_temp_output:usize = cast (Core.Num.impl_i32__count_ones hints_mask <: u32) <: usize in
  hint, hax_temp_output <: (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) & usize)

#pop-options

#push-options "--admit_smt_queries true"

let uuse_hint (gamma2: i32) (r hint: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let r0, r1:(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) &
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) =
    Libcrux_intrinsics.Avx2.mm256_setzero_si256 (), Libcrux_intrinsics.Avx2.mm256_setzero_si256 ()
    <:
    (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) &
      Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let tmp0, tmp1:(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) &
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) =
    decompose gamma2 r r0 r1
  in
  let r0:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) = tmp0 in
  let r1:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) = tmp1 in
  let _:Prims.unit = () in
  let all_zeros:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_setzero_si256 ()
  in
  let negate_hints:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.vec256_blendv_epi32 all_zeros hint r0
  in
  let negate_hints:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_slli_epi32 (mk_i32 1) negate_hints
  in
  let hints:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_sub_epi32 hint negate_hints
  in
  let r1_plus_hints:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_add_epi32 r1 hints
  in
  let hint, r1_plus_hints:(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) &
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) =
    match gamma2 <: i32 with
    | Rust_primitives.Integers.MkInt 95232 ->
      let max:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2.mm256_set1_epi32 (mk_i32 43)
      in
      let r1_plus_hints:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2.vec256_blendv_epi32 r1_plus_hints max r1_plus_hints
      in
      let greater_than_or_equal_to_max:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2.mm256_cmpgt_epi32 r1_plus_hints max
      in
      let hint:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2.vec256_blendv_epi32 r1_plus_hints
          all_zeros
          greater_than_or_equal_to_max
      in
      hint, r1_plus_hints
      <:
      (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) &
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    | Rust_primitives.Integers.MkInt 261888 ->
      let hint:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2.mm256_and_si256 r1_plus_hints
          (Libcrux_intrinsics.Avx2.mm256_set1_epi32 (mk_i32 15)
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      in
      hint, r1_plus_hints
      <:
      (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) &
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    | _ ->
      hint, r1_plus_hints
      <:
      (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) &
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  hint

#pop-options
