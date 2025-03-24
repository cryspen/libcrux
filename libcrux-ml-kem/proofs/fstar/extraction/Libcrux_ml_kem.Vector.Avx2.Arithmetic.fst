module Libcrux_ml_kem.Vector.Avx2.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
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

#push-options "--z3rlimit 100"

let cond_subtract_3329_ (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let field_modulus:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS
  in
  let _:Prims.unit = assert (forall i. get_lane field_modulus i == (mk_i16 3329)) in
  let vv_minus_field_modulus:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi16 vector field_modulus
  in
  let _:Prims.unit =
    assert (forall i. get_lane vv_minus_field_modulus i == get_lane vector i -. (mk_i16 3329))
  in
  let sign_mask:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srai_epi16 (mk_i32 15) vv_minus_field_modulus
  in
  let _:Prims.unit =
    assert (forall i. get_lane sign_mask i == (get_lane vv_minus_field_modulus i >>! (mk_i32 15)))
  in
  let conditional_add_field_modulus:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_and_si256 sign_mask field_modulus
  in
  let _:Prims.unit =
    assert (forall i.
          get_lane conditional_add_field_modulus i == (get_lane sign_mask i &. (mk_i16 3329)))
  in
  let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi16 vv_minus_field_modulus
      conditional_add_field_modulus
  in
  let _:Prims.unit =
    assert (forall i.
          get_lane result i ==
          (get_lane vv_minus_field_modulus i +. get_lane conditional_add_field_modulus i));
    assert (forall i. get_lane result i == Spec.Utils.cond_sub (get_lane vector i));
    assert (forall i.
          get_lane result i ==
          (if (get_lane vector i) >=. (mk_i16 3329)
            then get_lane vector i -! (mk_i16 3329)
            else get_lane vector i))
  in
  result

#pop-options

#push-options "--z3rlimit 200"

let barrett_reduce (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let t0:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mulhi_epi16 vector
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 v_BARRETT_MULTIPLIER
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let _:Prims.unit =
    assert (forall i.
          get_lane t0 i ==
          (cast (((cast (get_lane vector i) <: i32) *. (cast v_BARRETT_MULTIPLIER <: i32)) >>!
                (mk_i32 16))
            <:
            i16))
  in
  let t512:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 (mk_i16 512)
  in
  let _:Prims.unit = assert (forall i. get_lane t512 i == (mk_i16 512)) in
  let t1:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi16 t0 t512
  in
  let _:Prims.unit = assert (forall i. get_lane t1 i == get_lane t0 i +. (mk_i16 512)) in
  let quotient:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srai_epi16 (mk_i32 10) t1
  in
  let _:Prims.unit =
    assert (forall i. get_lane quotient i == (((get_lane t1 i) <: i16) >>! ((mk_i32 10) <: i32)))
  in
  let quotient_times_field_modulus:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi16 quotient
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let _:Prims.unit =
    assert (forall i.
          get_lane quotient_times_field_modulus i ==
          get_lane quotient i *. Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS)
  in
  let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi16 vector quotient_times_field_modulus
  in
  let _:Prims.unit =
    assert (forall i.
          get_lane result i == get_lane vector i -. get_lane quotient_times_field_modulus i);
    assert (forall i. get_lane result i == Spec.Utils.barrett_red (get_lane vector i));
    assert (forall i. v (get_lane result i) % 3329 == v (get_lane vector i) % 3329);
    assert (forall i. Spec.Utils.is_i16b 3328 (get_lane result i));
    assert (forall (i: nat). i < 16 ==> Spec.Utils.is_i16b 3328 (get_lane result i));
    assert (Spec.Utils.is_i16b_array 3328 (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 result))
  in
  result

#pop-options

#push-options "--z3rlimit 100 --ext context_pruning"

let montgomery_multiply_by_constant
      (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (constant: i16)
     =
  let vec_constant:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 constant
  in
  let _:Prims.unit = assert (forall i. get_lane vec_constant i == constant) in
  let value_low:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi16 vector vec_constant
  in
  let _:Prims.unit = assert (forall i. get_lane value_low i == get_lane vector i *. constant) in
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
  let _:Prims.unit =
    assert (forall i. get_lane k i == get_lane value_low i *. (neg (mk_i16 3327)))
  in
  let modulus:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS
  in
  let _:Prims.unit = assert (forall i. get_lane modulus i == (mk_i16 3329)) in
  let k_times_modulus:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mulhi_epi16 k modulus
  in
  let _:Prims.unit =
    assert (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 k_times_modulus ==
        Spec.Utils.map2 (fun x y ->
              cast (((cast x <: i32) *. (cast y <: i32)) >>! (mk_i32 16)) <: i16)
          (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 k)
          (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 modulus));
    assert (forall i.
          get_lane k_times_modulus i ==
          (cast (((cast (get_lane k i) <: i32) *. (cast (get_lane modulus i) <: i32)) >>!
                (mk_i32 16))
            <:
            i16))
  in
  let value_high:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mulhi_epi16 vector vec_constant
  in
  let _:Prims.unit =
    assert (forall i.
          get_lane value_high i ==
          (cast (((cast (get_lane vector i) <: i32) *. (cast (get_lane vec_constant i) <: i32)) >>!
                (mk_i32 16))
            <:
            i16))
  in
  let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi16 value_high k_times_modulus
  in
  let _:Prims.unit =
    Spec.Utils.lemma_range_at_percent 3329 (pow2 32);
    assert (v (cast (mk_i16 3329) <: i32) == (3329 @% pow2 32));
    assert (v (cast (mk_i16 3329) <: i32) == 3329);
    assert ((cast (mk_i16 3329) <: i32) == (mk_i32 3329));
    assert (forall i. get_lane result i == (get_lane value_high i) -. (get_lane k_times_modulus i));
    assert (forall i. get_lane result i == Spec.Utils.mont_mul_red_i16 (get_lane vector i) constant);
    assert (forall i. Spec.Utils.is_i16b 3328 (get_lane result i));
    assert (forall (i: nat). i < 16 ==> Spec.Utils.is_i16b 3328 (get_lane result i));
    assert (Spec.Utils.is_i16b_array 3328 (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 result));
    assert (forall i.
          v (get_lane result i) % 3329 == ((v (get_lane vector i) * v constant * 169) % 3329))
  in
  result

#pop-options

#push-options "--z3rlimit 100"

let montgomery_multiply_by_constants (vec constants: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let value_low:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi16 vec constants
  in
  let _:Prims.unit =
    assert (forall i. get_lane value_low i == get_lane vec i *. get_lane constants i)
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
  let _:Prims.unit =
    assert (forall i. get_lane k i == get_lane value_low i *. (neg (mk_i16 3327)))
  in
  let modulus:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS
  in
  let _:Prims.unit = assert (forall i. get_lane modulus i == (mk_i16 3329)) in
  let k_times_modulus:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mulhi_epi16 k modulus
  in
  let _:Prims.unit =
    assert (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 k_times_modulus ==
        Spec.Utils.map2 (fun x y ->
              cast (((cast x <: i32) *. (cast y <: i32)) >>! (mk_i32 16)) <: i16)
          (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 k)
          (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 modulus));
    assert (forall i.
          get_lane k_times_modulus i ==
          (cast (((cast (get_lane k i) <: i32) *. (cast (get_lane modulus i) <: i32)) >>!
                (mk_i32 16))
            <:
            i16))
  in
  let value_high:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mulhi_epi16 vec constants
  in
  let _:Prims.unit =
    assert (forall i.
          get_lane value_high i ==
          (cast (((cast (get_lane vec i) <: i32) *. (cast (get_lane constants i) <: i32)) >>!
                (mk_i32 16))
            <:
            i16))
  in
  let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi16 value_high k_times_modulus
  in
  let _:Prims.unit =
    Spec.Utils.lemma_range_at_percent 3329 (pow2 32);
    assert (v (cast (mk_i16 3329) <: i32) == (3329 @% pow2 32));
    assert (v (cast (mk_i16 3329) <: i32) == 3329);
    assert ((cast (mk_i16 3329) <: i32) == (mk_i32 3329));
    assert (forall i. get_lane result i == (get_lane value_high i) -. (get_lane k_times_modulus i));
    assert (forall i.
          get_lane result i == Spec.Utils.mont_mul_red_i16 (get_lane vec i) (get_lane constants i));
    assert (forall i. Spec.Utils.is_i16b 3328 (get_lane result i));
    assert (forall (i: nat). i < 16 ==> Spec.Utils.is_i16b 3328 (get_lane result i));
    assert (Spec.Utils.is_i16b_array 3328 (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 result));
    assert (forall i.
          v (get_lane result i) % 3329 ==
          ((v (get_lane vec i) * v (get_lane constants i) * 169) % 3329))
  in
  result

#pop-options

let montgomery_reduce_i32s (vec: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let k:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi16 vec
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
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi32 (mk_i32 16) vec
  in
  let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi16 value_high k_times_modulus
  in
  let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_slli_epi32 (mk_i32 16) result
  in
  let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srai_epi32 (mk_i32 16) result
  in
  let _:Prims.unit = admit () (* Panic freedom *) in
  result

#push-options "--z3rlimit 100"

let montgomery_multiply_m128i_by_constants (vec constants: Libcrux_intrinsics.Avx2_extract.t_Vec128) =
  let value_low:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_mullo_epi16 vec constants
  in
  let _:Prims.unit =
    assert (forall i. get_lane128 value_low i == get_lane128 vec i *. get_lane128 constants i)
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
  let _:Prims.unit =
    assert (forall i. get_lane128 k i == get_lane128 value_low i *. (neg (mk_i16 3327)))
  in
  let modulus:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_set1_epi16 Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS
  in
  let _:Prims.unit = assert (forall i. get_lane128 modulus i == (mk_i16 3329)) in
  let k_times_modulus:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_mulhi_epi16 k modulus
  in
  let _:Prims.unit =
    assert (Libcrux_intrinsics.Avx2_extract.vec128_as_i16x8 k_times_modulus ==
        Spec.Utils.map2 (fun x y ->
              cast (((cast x <: i32) *. (cast y <: i32)) >>! (mk_i32 16)) <: i16)
          (Libcrux_intrinsics.Avx2_extract.vec128_as_i16x8 k)
          (Libcrux_intrinsics.Avx2_extract.vec128_as_i16x8 modulus));
    assert (forall i.
          get_lane128 k_times_modulus i ==
          (cast (((cast (get_lane128 k i) <: i32) *. (cast (get_lane128 modulus i) <: i32)) >>!
                (mk_i32 16))
            <:
            i16))
  in
  let value_high:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_mulhi_epi16 vec constants
  in
  let _:Prims.unit =
    assert (forall i.
          get_lane128 value_high i ==
          (cast (((cast (get_lane128 vec i) <: i32) *. (cast (get_lane128 constants i) <: i32)) >>!
                (mk_i32 16))
            <:
            i16))
  in
  let result:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_sub_epi16 value_high k_times_modulus
  in
  let _:Prims.unit =
    Spec.Utils.lemma_range_at_percent 3329 (pow2 32);
    assert (v (cast (mk_i16 3329) <: i32) == (3329 @% pow2 32));
    assert (v (cast (mk_i16 3329) <: i32) == 3329);
    assert ((cast (mk_i16 3329) <: i32) == (mk_i32 3329));
    assert (forall i.
          get_lane128 result i == (get_lane128 value_high i) -. (get_lane128 k_times_modulus i));
    assert (forall i.
          get_lane128 result i ==
          Spec.Utils.mont_mul_red_i16 (get_lane128 vec i) (get_lane128 constants i));
    assert (forall i. Spec.Utils.is_i16b 3328 (get_lane128 result i));
    assert (forall (i: nat). i < 8 ==> Spec.Utils.is_i16b 3328 (get_lane128 result i));
    assert (Spec.Utils.is_i16b_array 3328 (Libcrux_intrinsics.Avx2_extract.vec128_as_i16x8 result));
    assert (forall i.
          v (get_lane128 result i) % 3329 ==
          ((v (get_lane128 vec i) * v (get_lane128 constants i) * 169) % 3329))
  in
  result

#pop-options

#push-options "--admit_smt_queries true"

let to_unsigned_representative (a: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let t:Libcrux_intrinsics.Avx2_extract.t_Vec256 = shift_right (mk_i32 15) a in
  let fm:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    bitwise_and_with_constant t Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS
  in
  add a fm

#pop-options
