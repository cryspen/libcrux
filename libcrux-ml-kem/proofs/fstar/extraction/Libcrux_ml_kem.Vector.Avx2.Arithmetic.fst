module Libcrux_ml_kem.Vector.Avx2.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let lemma_add_i (lhs rhs: t_Vec256) (i:nat): Lemma 
  (requires (i < 16 /\ Spec.Utils.is_intb (pow2 15 - 1) (v (get_lane lhs i) + v (get_lane rhs i))))
  (ensures (v (add_mod (get_lane lhs i) (get_lane rhs i)) ==
            (v (get_lane lhs i) + v (get_lane rhs i))))
  [SMTPat (v (add_mod (get_lane lhs i) (get_lane rhs i)))] = ()

let add (lhs rhs: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi16 lhs rhs
  in
  let _:Prims.unit =
    assert (forall i. get_lane result i == get_lane lhs i +. get_lane rhs i);
    assert (forall i. v (get_lane result i) == v (get_lane lhs i) + v (get_lane rhs i))
  in
  result

let bitwise_and_with_constant (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) (constant: i16) =
  let cv:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 constant
  in
  let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_and_si256 vector cv
  in
  let _:Prims.unit =
    Seq.lemma_eq_intro (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 result)
      (Spec.Utils.map_array (fun x -> x &. constant)
          (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 vector))
  in
  result

let lemma_mul_i (lhs: t_Vec256) (i:nat) (c:i16):  Lemma 
  (requires (i < 16 /\ Spec.Utils.is_intb (pow2 15 - 1) (v (get_lane lhs i) * v c)))
  (ensures (v (mul_mod (get_lane lhs i) c) ==
            (v (get_lane lhs i) * v c)))
  [SMTPat (v (mul_mod (get_lane lhs i) c))] = ()

let multiply_by_constant (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) (constant: i16) =
  let cv:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 constant
  in
  let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi16 vector cv
  in
  let _:Prims.unit =
    Seq.lemma_eq_intro (vec256_as_i16x16 result)
      (Spec.Utils.map_array (fun x -> x *. constant)
          (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 vector))
  in
  let _:Prims.unit =
    assert (forall i. get_lane result i == get_lane vector i *. constant);
    assert (forall i. v (get_lane vector i *. constant) == v (get_lane vector i) * v constant);
    assert (forall i. v (get_lane result i) == v (get_lane vector i) * v constant)
  in
  result

let shift_right (v_SHIFT_BY: i32) (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srai_epi16 v_SHIFT_BY vector
  in
  let _:Prims.unit =
    Seq.lemma_eq_intro (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 result)
      (Spec.Utils.map_array (fun x -> x >>! v_SHIFT_BY)
          (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 vector))
  in
  result

let lemma_sub_i (lhs rhs: t_Vec256) (i:nat):  Lemma 
  (requires (i < 16 /\ Spec.Utils.is_intb (pow2 15 - 1) (v (get_lane lhs i) - v (get_lane rhs i))))
  (ensures (v (sub_mod (get_lane lhs i) (get_lane rhs i)) ==
            (v (get_lane lhs i) - v (get_lane rhs i))))
  [SMTPat (v (sub_mod (get_lane lhs i) (get_lane rhs i)))] = ()

let sub (lhs rhs: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi16 lhs rhs
  in
  let _:Prims.unit =
    assert (forall i. get_lane result i == get_lane lhs i -. get_lane rhs i);
    assert (forall i. v (get_lane result i) == v (get_lane lhs i) - v (get_lane rhs i))
  in
  result

let barrett_reduce (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let t:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mulhi_epi16 vector
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 v_BARRETT_MULTIPLIER
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let t:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi16 t
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 512s
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let quotient:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srai_epi16 10l t
  in
  let quotient_times_field_modulus:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi16 quotient
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  Libcrux_intrinsics.Avx2_extract.mm256_sub_epi16 vector quotient_times_field_modulus

let cond_subtract_3329_ (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let field_modulus:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS
  in
  let vv_minus_field_modulus:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi16 vector field_modulus
  in
  let sign_mask:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srai_epi16 15l vv_minus_field_modulus
  in
  let conditional_add_field_modulus:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_and_si256 sign_mask field_modulus
  in
  let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi16 vv_minus_field_modulus
      conditional_add_field_modulus
  in
  let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 = result in
  let _:Prims.unit = admit () (* Panic freedom *) in
  result

let montgomery_multiply_by_constant
      (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (constant: i16)
     =
  let constant:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 constant
  in
  let value_low:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi16 vector constant
  in
  let k:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi16 value_low
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 (cast (Libcrux_ml_kem.Vector.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
                <:
                u32)
            <:
            i16)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let k_times_modulus:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mulhi_epi16 k
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let value_high:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mulhi_epi16 vector constant
  in
  Libcrux_intrinsics.Avx2_extract.mm256_sub_epi16 value_high k_times_modulus

let montgomery_multiply_by_constants (v c: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let value_low:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi16 v c
  in
  let k:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi16 value_low
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 (cast (Libcrux_ml_kem.Vector.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
                <:
                u32)
            <:
            i16)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let k_times_modulus:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mulhi_epi16 k
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let value_high:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mulhi_epi16 v c
  in
  Libcrux_intrinsics.Avx2_extract.mm256_sub_epi16 value_high k_times_modulus

let montgomery_multiply_m128i_by_constants (v c: Libcrux_intrinsics.Avx2_extract.t_Vec128) =
  let value_low:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_mullo_epi16 v c
  in
  let k:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_mullo_epi16 value_low
      (Libcrux_intrinsics.Avx2_extract.mm_set1_epi16 (cast (Libcrux_ml_kem.Vector.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
                <:
                u32)
            <:
            i16)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec128)
  in
  let k_times_modulus:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_mulhi_epi16 k
      (Libcrux_intrinsics.Avx2_extract.mm_set1_epi16 Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec128)
  in
  let value_high:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_mulhi_epi16 v c
  in
  Libcrux_intrinsics.Avx2_extract.mm_sub_epi16 value_high k_times_modulus

let montgomery_reduce_i32s (v: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let k:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi16 v
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (cast (Libcrux_ml_kem.Vector.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
                <:
                u32)
            <:
            i32)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let k_times_modulus:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mulhi_epi16 k
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (cast (Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS
                <:
                i16)
            <:
            i32)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let value_high:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi32 16l v
  in
  let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi16 value_high k_times_modulus
  in
  let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_slli_epi32 16l result
  in
  Libcrux_intrinsics.Avx2_extract.mm256_srai_epi32 16l result
