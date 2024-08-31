module Libcrux_ml_kem.Vector.Avx2.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let add (lhs rhs: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  Libcrux_intrinsics.Avx2_extract.mm256_add_epi16 lhs rhs

let bitwise_and_with_constant (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) (constant: i16) =
  let cv:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 constant
  in
  let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_and_si256 vector cv
  in
  let _:Prims.unit =
    Spec.Utils.lemma_map2_index #_
      #_
      #_
      #(sz 16)
      ( &. )
      (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 vector)
      (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 cv);
    Spec.Utils.lemma_map_index #_
      #_
      #(sz 16)
      (fun x -> x &. constant)
      (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 vector);
    Spec.Utils.lemma_create_index #_ (sz 16) constant;
    Seq.lemma_eq_intro (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 result)
      (Spec.Utils.map_array (fun x -> x &. constant)
          (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 vector))
  in
  result

let multiply_by_constant (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) (constant: i16) =
  let cv:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 constant
  in
  let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi16 vector cv
  in
  let _:Prims.unit =
    Spec.Utils.lemma_map2_index #_
      #_
      #_
      #(sz 16)
      mul_mod
      (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 vector)
      (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 cv);
    Spec.Utils.lemma_map_index #_
      #_
      #(sz 16)
      (fun x -> x *. constant)
      (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 vector);
    Spec.Utils.lemma_create_index #_ (sz 16) constant;
    Seq.lemma_eq_intro (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 result)
      (Spec.Utils.map_array (fun x -> x *. constant)
          (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 vector))
  in
  result

let shift_right (v_SHIFT_BY: i32) (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srai_epi16 v_SHIFT_BY vector
  in
  let _:Prims.unit =
    Spec.Utils.lemma_map_index #_
      #_
      #(sz 16)
      (fun x -> x >>! v_SHIFT_BY)
      (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 vector);
    Seq.lemma_eq_intro (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 result)
      (Spec.Utils.map_array (fun x -> x >>! v_SHIFT_BY)
          (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 vector))
  in
  result

let sub (lhs rhs: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  Libcrux_intrinsics.Avx2_extract.mm256_sub_epi16 lhs rhs

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

let get_ith v i = Seq.index (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 v) i

#push-options "--z3rlimit 500"
let cond_subtract_3329_ (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let field_modulus:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS
  in
  let _:Prims.unit =
    Spec.Utils.lemma_create_index #_ (sz 16) Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS
  in
  let vv_minus_field_modulus:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi16 vector field_modulus
  in
  let _:Prims.unit =
    Spec.Utils.lemma_map2_index #_
      #_
      #_
      #(sz 16)
      ( -. )
      (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 vector)
      (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 field_modulus)
  in
  assume (forall i. Spec.Utils.is_i16b (pow2 12 - 1) (get_ith vector i));
  assert (forall i. get_ith vv_minus_field_modulus i == get_ith vector i -. 3329s);
  assert (forall i. v (get_ith vv_minus_field_modulus i) == v (get_ith vector i) - 3329);
  let sign_mask:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srai_epi16 15l vv_minus_field_modulus
  in
  let _:Prims.unit =
    Spec.Utils.lemma_map_index #_
      #_
      #(sz 16)
      (fun x -> x >>! 15l)
      (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 vv_minus_field_modulus)
  in
  assume (forall (x:i16). v x < 0 ==> x >>! 15l == ones);
  assume (forall (x:i16). v x >= 0 ==> x >>! 15l == 0s);
  assert (forall i. get_ith sign_mask i == ((get_ith vv_minus_field_modulus i) >>! 15l));
  assert (forall i. get_ith sign_mask i == 
               (if (v (get_ith vector i) - 3329) < 0 then ones else 0s));
  let conditional_add_field_modulus:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_and_si256 sign_mask field_modulus
  in
  let _:Prims.unit =
    Spec.Utils.lemma_map2_index #_
      #_
      #_
      #(sz 16)
      ( &. )
      (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 sign_mask)
      (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 field_modulus)
  in
  assume (forall (x:i16). (x &. ones) == x);
  assume (forall (x:i16). (x &. 0s) == 0s);
  assume (forall (x:i16). (ones &. x) == x);
  assume (forall (x:i16). (0s &. x) == 0s);
  assert (forall i. get_ith conditional_add_field_modulus i == 
               (if (v (get_ith vector i) - 3329) < 0 then 3329s else 0s));
  let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi16 vv_minus_field_modulus
      conditional_add_field_modulus
  in
  let _:Prims.unit =
    Spec.Utils.lemma_map2_index #_
      #_
      #_
      #(sz 16)
      ( +. )
      (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 vv_minus_field_modulus)
      (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 conditional_add_field_modulus)
  in
  let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 = result in
  assert (forall i. get_ith result i == 
               (if (v (get_ith vector i) - 3329) < 0 then get_ith vector i else get_ith vector i -. 3329s));
  assert (forall i. get_ith result i == 
               (if (get_ith vector i) >=. 3329s then get_ith vector i -. 3329s else get_ith vector i));
  assert (forall i. get_ith result i ==  (fun x -> if x >=. 3329s then x -! 3329s else x) (get_ith vector i));
  Spec.Utils.lemma_map_index #_ #_ #(sz 16) (fun x -> if x >=. 3329s then x -! 3329s else x)
    (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 vector);
  assert (forall i. Seq.index
    (Spec.Utils.map_array (fun x -> if x >=. 3329s then x -! 3329s else x)
            (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 vector)) i == 
            (fun x -> if x >=. 3329s then x -! 3329s else x) (get_ith vector i));
  Seq.lemma_eq_intro (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 result)
   (Spec.Utils.map_array (fun x -> if x >=. 3329s then x -! 3329s else x)
            (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 vector));
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
