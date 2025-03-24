module Libcrux_intrinsics.Avx2_extract
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

unfold type t_Vec256 = bit_vec 256
val vec256_as_i16x16 (x: bit_vec 256) : t_Array i16 (sz 16)
let get_lane (v: bit_vec 256) (i:nat{i < 16}) = Seq.index (vec256_as_i16x16 v) i

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl:Core.Clone.t_Clone t_Vec256

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_1:Core.Marker.t_Copy t_Vec256

unfold type t_Vec128 = bit_vec 128
val vec128_as_i16x8 (x: bit_vec 128) : t_Array i16 (sz 8)
let get_lane128 (v: bit_vec 128) (i:nat{i < 8}) = Seq.index (vec128_as_i16x8 v) i

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_3:Core.Clone.t_Clone t_Vec128

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_2:Core.Marker.t_Copy t_Vec128

val mm256_storeu_si256_u8 (output: t_Slice u8) (vector: t_Vec256)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

val mm256_storeu_si256_i16 (output: t_Slice i16) (vector: t_Vec256)
    : Prims.Pure (t_Slice i16)
      Prims.l_True
      (ensures
        fun output_future ->
          let output_future:t_Slice i16 = output_future in
          (Core.Slice.impl__len #i16 output_future <: usize) =.
          (Core.Slice.impl__len #i16 output <: usize))

val mm256_storeu_si256_i32 (output: t_Slice i32) (vector: t_Vec256)
    : Prims.Pure (t_Slice i32) Prims.l_True (fun _ -> Prims.l_True)

val mm_storeu_si128 (output: t_Slice i16) (vector: t_Vec128)
    : Prims.Pure (t_Slice i16) Prims.l_True (fun _ -> Prims.l_True)

val mm_storeu_si128_i32 (output: t_Slice i32) (vector: t_Vec128)
    : Prims.Pure (t_Slice i32) Prims.l_True (fun _ -> Prims.l_True)

include BitVec.Intrinsics {mm_storeu_bytes_si128}

include BitVec.Intrinsics {mm_loadu_si128}

val mm256_loadu_si256_u8 (input: t_Slice u8)
    : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val mm256_loadu_si256_i16 (input: t_Slice i16)
    : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val mm256_loadu_si256_i32 (input: t_Slice i32)
    : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val mm256_setzero_si256: Prims.unit
  -> Prims.Pure t_Vec256
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Vec256 = result in
          vec256_as_i16x16 result == Seq.create 16 (mk_i16 0))

val mm256_set_m128i (hi lo: t_Vec128) : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

include BitVec.Intrinsics {mm_set_epi8}

include BitVec.Intrinsics {mm256_set_epi8}

include BitVec.Intrinsics {mm256_set1_epi16 as mm256_set1_epi16}
val lemma_mm256_set1_epi16 constant
  : Lemma (   vec256_as_i16x16 (mm256_set1_epi16 constant)
           == Spec.Utils.create (sz 16) constant
          )
          [SMTPat (vec256_as_i16x16 (mm256_set1_epi16 constant))]

include BitVec.Intrinsics {mm256_set_epi16 as mm256_set_epi16}
let lemma_mm256_set_epi16 v15 v14 v13 v12 v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 :
    Lemma (vec256_as_i16x16 (mm256_set_epi16 v15 v14 v13 v12 v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0) == 
            Spec.Utils.create16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15)
            [SMTPat (vec256_as_i16x16 (mm256_set_epi16 v15 v14 v13 v12 v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0))] = admit()

val mm_set1_epi16 (constant: i16)
    : Prims.Pure t_Vec128
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Vec128 = result in
          vec128_as_i16x8 result == Spec.Utils.create (sz 8) constant)

val mm256_set1_epi32 (constant: i32) : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val mm_set_epi32 (input3 input2 input1 input0: i32)
    : Prims.Pure t_Vec128 Prims.l_True (fun _ -> Prims.l_True)

include BitVec.Intrinsics {mm256_set_epi32}

val mm_add_epi16 (lhs rhs: t_Vec128)
    : Prims.Pure t_Vec128
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Vec128 = result in
          vec128_as_i16x8 result ==
          Spec.Utils.map2 ( +. ) (vec128_as_i16x8 lhs) (vec128_as_i16x8 rhs))

val mm_sub_epi16 (lhs rhs: t_Vec128)
    : Prims.Pure t_Vec128
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Vec128 = result in
          vec128_as_i16x8 result ==
          Spec.Utils.map2 ( -. ) (vec128_as_i16x8 lhs) (vec128_as_i16x8 rhs))

val mm256_add_epi16 (lhs rhs: t_Vec256)
    : Prims.Pure t_Vec256
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Vec256 = result in
          vec256_as_i16x16 result ==
          Spec.Utils.map2 ( +. ) (vec256_as_i16x16 lhs) (vec256_as_i16x16 rhs))

include BitVec.Intrinsics {mm256_madd_epi16 as mm256_madd_epi16}

val mm256_add_epi32 (lhs rhs: t_Vec256) : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val mm256_sub_epi16 (lhs rhs: t_Vec256)
    : Prims.Pure t_Vec256
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Vec256 = result in
          vec256_as_i16x16 result ==
          Spec.Utils.map2 ( -. ) (vec256_as_i16x16 lhs) (vec256_as_i16x16 rhs))

val mm256_add_epi64 (lhs rhs: t_Vec256) : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val mm256_abs_epi32 (a: t_Vec256) : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val mm256_sub_epi32 (lhs rhs: t_Vec256) : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

include BitVec.Intrinsics {mm256_mullo_epi16 as mm256_mullo_epi16}
let lemma_mm256_mullo_epi16 v1 v2 :
   Lemma (vec256_as_i16x16 (mm256_mullo_epi16 v1 v2) == 
       Spec.Utils.map2 mul_mod (vec256_as_i16x16 v1) (vec256_as_i16x16 v2))
       [SMTPat (vec256_as_i16x16 (mm256_mullo_epi16 v1 v2))] = admit()

val mm_mullo_epi16 (lhs rhs: t_Vec128)
    : Prims.Pure t_Vec128
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Vec128 = result in
          vec128_as_i16x8 result ==
          Spec.Utils.map2 mul_mod (vec128_as_i16x8 lhs) (vec128_as_i16x8 rhs))

val mm256_cmpgt_epi16 (lhs rhs: t_Vec256) : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val mm256_cmpgt_epi32 (lhs rhs: t_Vec256) : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val mm256_cmpeq_epi32 (a b: t_Vec256) : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val mm256_sign_epi32 (a b: t_Vec256) : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val mm256_castsi256_ps (a: t_Vec256) : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val mm256_movemask_ps (a: u8) : Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

val mm_mulhi_epi16 (lhs rhs: t_Vec128)
    : Prims.Pure t_Vec128
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Vec128 = result in
          vec128_as_i16x8 result ==
          Spec.Utils.map2 (fun x y ->
                cast (((cast x <: i32) *. (cast y <: i32)) >>! (mk_i32 16)) <: i16)
            (vec128_as_i16x8 lhs)
            (vec128_as_i16x8 rhs))

val mm256_mullo_epi32 (lhs rhs: t_Vec256) : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val mm256_mulhi_epi16 (lhs rhs: t_Vec256)
    : Prims.Pure t_Vec256
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Vec256 = result in
          vec256_as_i16x16 result ==
          Spec.Utils.map2 (fun x y ->
                cast (((cast x <: i32) *. (cast y <: i32)) >>! (mk_i32 16)) <: i16)
            (vec256_as_i16x16 lhs)
            (vec256_as_i16x16 rhs))

val mm256_mul_epu32 (lhs rhs: t_Vec256) : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val mm256_mul_epi32 (lhs rhs: t_Vec256) : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

include BitVec.Intrinsics {mm256_and_si256 as mm256_and_si256}
val lemma_mm256_and_si256 lhs rhs
  : Lemma (   vec256_as_i16x16 (mm256_and_si256 lhs rhs)
           == Spec.Utils.map2 (&.) (vec256_as_i16x16 lhs) (vec256_as_i16x16 rhs)
          )
          [SMTPat (vec256_as_i16x16 (mm256_and_si256 lhs rhs))]

val mm256_or_si256 (a b: t_Vec256) : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val mm256_testz_si256 (lhs rhs: t_Vec256) : Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

val mm256_xor_si256 (lhs rhs: t_Vec256) : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val mm256_srai_epi16 (v_SHIFT_BY: i32) (vector: t_Vec256)
    : Prims.Pure t_Vec256
      (requires v_SHIFT_BY >=. mk_i32 0 && v_SHIFT_BY <. mk_i32 16)
      (ensures
        fun result ->
          let result:t_Vec256 = result in
          vec256_as_i16x16 result ==
          Spec.Utils.map_array (fun x -> x >>! v_SHIFT_BY) (vec256_as_i16x16 vector))

val mm256_srai_epi32 (v_SHIFT_BY: i32) (vector: t_Vec256)
    : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

include BitVec.Intrinsics {mm256_srli_epi16 as mm256_srli_epi16}

val mm256_srli_epi32 (v_SHIFT_BY: i32) (vector: t_Vec256)
    : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val mm_srli_epi64 (v_SHIFT_BY: i32) (vector: t_Vec128)
    : Prims.Pure t_Vec128 Prims.l_True (fun _ -> Prims.l_True)

include BitVec.Intrinsics {mm256_srli_epi64 as mm256_srli_epi64}

include BitVec.Intrinsics {mm256_slli_epi16 as mm256_slli_epi16}

val mm256_slli_epi32 (v_SHIFT_BY: i32) (vector: t_Vec256)
    : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

include BitVec.Intrinsics {mm_shuffle_epi8}

include BitVec.Intrinsics {mm256_shuffle_epi8}

val mm256_shuffle_epi32 (v_CONTROL: i32) (vector: t_Vec256)
    : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val mm256_permute4x64_epi64 (v_CONTROL: i32) (vector: t_Vec256)
    : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val mm256_unpackhi_epi64 (lhs rhs: t_Vec256)
    : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val mm256_unpacklo_epi32 (lhs rhs: t_Vec256)
    : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val mm256_unpackhi_epi32 (lhs rhs: t_Vec256)
    : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

include BitVec.Intrinsics {mm256_castsi256_si128 as mm256_castsi256_si128}

val mm256_castsi128_si256 (vector: t_Vec128)
    : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val mm256_cvtepi16_epi32 (vector: t_Vec128)
    : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

include BitVec.Intrinsics {mm_packs_epi16 as mm_packs_epi16}

val mm256_packs_epi32 (lhs rhs: t_Vec256) : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

include BitVec.Intrinsics {mm256_extracti128_si256 as mm256_extracti128_si256}

val mm256_inserti128_si256 (v_CONTROL: i32) (vector: t_Vec256) (vector_i128: t_Vec128)
    : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val mm256_blend_epi16 (v_CONTROL: i32) (lhs rhs: t_Vec256)
    : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val mm256_blend_epi32 (v_CONTROL: i32) (lhs rhs: t_Vec256)
    : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val vec256_blendv_epi32 (a b mask: t_Vec256)
    : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

include BitVec.Intrinsics {mm_movemask_epi8 as mm_movemask_epi8}

include BitVec.Intrinsics {mm256_permutevar8x32_epi32}

val mm256_srlv_epi32 (vector counts: t_Vec256)
    : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val mm256_srlv_epi64 (vector counts: t_Vec256)
    : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val mm_sllv_epi32 (vector counts: t_Vec128)
    : Prims.Pure t_Vec128 Prims.l_True (fun _ -> Prims.l_True)

include BitVec.Intrinsics {mm256_sllv_epi32}

val mm256_slli_epi64 (v_LEFT: i32) (x: t_Vec256)
    : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val mm256_bsrli_epi128 (v_SHIFT_BY: i32) (x: t_Vec256)
    : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val mm256_andnot_si256 (a b: t_Vec256) : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val mm256_set1_epi64x (a: i64) : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val mm256_set_epi64x (input3 input2 input1 input0: i64)
    : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val mm256_unpacklo_epi64 (a b: t_Vec256) : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val mm256_permute2x128_si256 (v_IMM8: i32) (a b: t_Vec256)
    : Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)
