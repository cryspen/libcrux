module Libcrux_intrinsics.Avx2_extract
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl': Core.Clone.t_Clone t_Vec256

let impl = impl'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Core.Marker.t_Copy t_Vec256

let impl_1 = impl_1'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': Core.Clone.t_Clone t_Vec128

let impl_3 = impl_3'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': Core.Marker.t_Copy t_Vec128

let impl_2 = impl_2'

assume
val mm256_storeu_si256_u8': output: t_Slice u8 -> vector: t_Vec256
  -> Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

let mm256_storeu_si256_u8 = mm256_storeu_si256_u8'

assume
val mm256_storeu_si256_i16': output: t_Slice i16 -> vector: t_Vec256
  -> Prims.Pure (t_Slice i16)
      Prims.l_True
      (ensures
        fun output_future ->
          let output_future:t_Slice i16 = output_future in
          (Core.Slice.impl__len #i16 output_future <: usize) =.
          (Core.Slice.impl__len #i16 output <: usize))

let mm256_storeu_si256_i16 = mm256_storeu_si256_i16'

assume
val mm256_storeu_si256_i32': output: t_Slice i32 -> vector: t_Vec256
  -> Prims.Pure (t_Slice i32) Prims.l_True (fun _ -> Prims.l_True)

let mm256_storeu_si256_i32 = mm256_storeu_si256_i32'

assume
val mm_storeu_si128': output: t_Slice i16 -> vector: t_Vec128
  -> Prims.Pure (t_Slice i16) Prims.l_True (fun _ -> Prims.l_True)

let mm_storeu_si128 = mm_storeu_si128'

assume
val mm_storeu_si128_i32': output: t_Slice i32 -> vector: t_Vec128
  -> Prims.Pure (t_Slice i32) Prims.l_True (fun _ -> Prims.l_True)

let mm_storeu_si128_i32 = mm_storeu_si128_i32'

assume
val mm256_loadu_si256_u8': input: t_Slice u8
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_loadu_si256_u8 = mm256_loadu_si256_u8'

assume
val mm256_loadu_si256_i16': input: t_Slice i16
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_loadu_si256_i16 = mm256_loadu_si256_i16'

assume
val mm256_loadu_si256_i32': input: t_Slice i32
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_loadu_si256_i32 = mm256_loadu_si256_i32'

assume
val mm256_setzero_si256': Prims.unit -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_setzero_si256 = mm256_setzero_si256'

assume
val mm256_set_m128i': hi: t_Vec128 -> lo: t_Vec128
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_set_m128i = mm256_set_m128i'

assume
val mm_set1_epi16': constant: i16
  -> Prims.Pure t_Vec128
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Vec128 = result in
          vec128_as_i16x8 result == Spec.Utils.create (sz 8) constant)

let mm_set1_epi16 = mm_set1_epi16'

assume
val mm256_set1_epi32': constant: i32 -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_set1_epi32 = mm256_set1_epi32'

assume
val mm_set_epi32': input3: i32 -> input2: i32 -> input1: i32 -> input0: i32
  -> Prims.Pure t_Vec128 Prims.l_True (fun _ -> Prims.l_True)

let mm_set_epi32 = mm_set_epi32'

assume
val mm_add_epi16': lhs: t_Vec128 -> rhs: t_Vec128
  -> Prims.Pure t_Vec128
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Vec128 = result in
          vec128_as_i16x8 result ==
          Spec.Utils.map2 ( +. ) (vec128_as_i16x8 lhs) (vec128_as_i16x8 rhs))

let mm_add_epi16 = mm_add_epi16'

assume
val mm_sub_epi16': lhs: t_Vec128 -> rhs: t_Vec128
  -> Prims.Pure t_Vec128
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Vec128 = result in
          vec128_as_i16x8 result ==
          Spec.Utils.map2 ( -. ) (vec128_as_i16x8 lhs) (vec128_as_i16x8 rhs))

let mm_sub_epi16 = mm_sub_epi16'

assume
val mm256_add_epi16': lhs: t_Vec256 -> rhs: t_Vec256
  -> Prims.Pure t_Vec256
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Vec256 = result in
          vec256_as_i16x16 result ==
          Spec.Utils.map2 ( +. ) (vec256_as_i16x16 lhs) (vec256_as_i16x16 rhs))

let mm256_add_epi16 = mm256_add_epi16'

assume
val mm256_add_epi32': lhs: t_Vec256 -> rhs: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_add_epi32 = mm256_add_epi32'

assume
val mm256_sub_epi16': lhs: t_Vec256 -> rhs: t_Vec256
  -> Prims.Pure t_Vec256
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Vec256 = result in
          vec256_as_i16x16 result ==
          Spec.Utils.map2 ( -. ) (vec256_as_i16x16 lhs) (vec256_as_i16x16 rhs))

let mm256_sub_epi16 = mm256_sub_epi16'

assume
val mm256_add_epi64': lhs: t_Vec256 -> rhs: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_add_epi64 = mm256_add_epi64'

assume
val mm256_abs_epi32': a: t_Vec256 -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_abs_epi32 = mm256_abs_epi32'

assume
val mm256_sub_epi32': lhs: t_Vec256 -> rhs: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_sub_epi32 = mm256_sub_epi32'

assume
val mm_mullo_epi16': lhs: t_Vec128 -> rhs: t_Vec128
  -> Prims.Pure t_Vec128
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Vec128 = result in
          vec128_as_i16x8 result ==
          Spec.Utils.map2 mul_mod (vec128_as_i16x8 lhs) (vec128_as_i16x8 rhs))

let mm_mullo_epi16 = mm_mullo_epi16'

assume
val mm256_cmpgt_epi16': lhs: t_Vec256 -> rhs: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_cmpgt_epi16 = mm256_cmpgt_epi16'

assume
val mm256_cmpgt_epi32': lhs: t_Vec256 -> rhs: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_cmpgt_epi32 = mm256_cmpgt_epi32'

assume
val mm256_cmpeq_epi32': a: t_Vec256 -> b: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_cmpeq_epi32 = mm256_cmpeq_epi32'

assume
val mm256_sign_epi32': a: t_Vec256 -> b: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_sign_epi32 = mm256_sign_epi32'

assume
val mm256_castsi256_ps': a: t_Vec256 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm256_castsi256_ps = mm256_castsi256_ps'

assume
val mm256_movemask_ps': a: u8 -> Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

let mm256_movemask_ps = mm256_movemask_ps'

assume
val mm_mulhi_epi16': lhs: t_Vec128 -> rhs: t_Vec128
  -> Prims.Pure t_Vec128
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Vec128 = result in
          vec128_as_i16x8 result ==
          Spec.Utils.map2 (fun x y ->
                cast (((cast x <: i32) *. (cast y <: i32)) >>! (mk_i32 16)) <: i16)
            (vec128_as_i16x8 lhs)
            (vec128_as_i16x8 rhs))

let mm_mulhi_epi16 = mm_mulhi_epi16'

assume
val mm256_mullo_epi32': lhs: t_Vec256 -> rhs: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_mullo_epi32 = mm256_mullo_epi32'

assume
val mm256_mulhi_epi16': lhs: t_Vec256 -> rhs: t_Vec256
  -> Prims.Pure t_Vec256
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Vec256 = result in
          vec256_as_i16x16 result ==
          Spec.Utils.map2 (fun x y ->
                cast (((cast x <: i32) *. (cast y <: i32)) >>! (mk_i32 16)) <: i16)
            (vec256_as_i16x16 lhs)
            (vec256_as_i16x16 rhs))

let mm256_mulhi_epi16 = mm256_mulhi_epi16'

assume
val mm256_mul_epu32': lhs: t_Vec256 -> rhs: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_mul_epu32 = mm256_mul_epu32'

assume
val mm256_mul_epi32': lhs: t_Vec256 -> rhs: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_mul_epi32 = mm256_mul_epi32'

assume
val mm256_or_si256': a: t_Vec256 -> b: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_or_si256 = mm256_or_si256'

assume
val mm256_testz_si256': lhs: t_Vec256 -> rhs: t_Vec256
  -> Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

let mm256_testz_si256 = mm256_testz_si256'

assume
val mm256_xor_si256': lhs: t_Vec256 -> rhs: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_xor_si256 = mm256_xor_si256'

assume
val mm256_srai_epi16': v_SHIFT_BY: i32 -> vector: t_Vec256
  -> Prims.Pure t_Vec256
      (requires v_SHIFT_BY >=. mk_i32 0 && v_SHIFT_BY <. mk_i32 16)
      (ensures
        fun result ->
          let result:t_Vec256 = result in
          vec256_as_i16x16 result ==
          Spec.Utils.map_array (fun x -> x >>! v_SHIFT_BY) (vec256_as_i16x16 vector))

let mm256_srai_epi16 (v_SHIFT_BY: i32) = mm256_srai_epi16' v_SHIFT_BY

assume
val mm256_srai_epi32': v_SHIFT_BY: i32 -> vector: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_srai_epi32 (v_SHIFT_BY: i32) = mm256_srai_epi32' v_SHIFT_BY

assume
val mm256_srli_epi32': v_SHIFT_BY: i32 -> vector: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_srli_epi32 (v_SHIFT_BY: i32) = mm256_srli_epi32' v_SHIFT_BY

assume
val mm_srli_epi64': v_SHIFT_BY: i32 -> vector: t_Vec128
  -> Prims.Pure t_Vec128 Prims.l_True (fun _ -> Prims.l_True)

let mm_srli_epi64 (v_SHIFT_BY: i32) = mm_srli_epi64' v_SHIFT_BY

assume
val mm256_slli_epi32': v_SHIFT_BY: i32 -> vector: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_slli_epi32 (v_SHIFT_BY: i32) = mm256_slli_epi32' v_SHIFT_BY

assume
val mm256_shuffle_epi32': v_CONTROL: i32 -> vector: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_shuffle_epi32 (v_CONTROL: i32) = mm256_shuffle_epi32' v_CONTROL

assume
val mm256_permute4x64_epi64': v_CONTROL: i32 -> vector: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_permute4x64_epi64 (v_CONTROL: i32) = mm256_permute4x64_epi64' v_CONTROL

assume
val mm256_unpackhi_epi64': lhs: t_Vec256 -> rhs: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_unpackhi_epi64 = mm256_unpackhi_epi64'

assume
val mm256_unpacklo_epi32': lhs: t_Vec256 -> rhs: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_unpacklo_epi32 = mm256_unpacklo_epi32'

assume
val mm256_unpackhi_epi32': lhs: t_Vec256 -> rhs: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_unpackhi_epi32 = mm256_unpackhi_epi32'

assume
val mm256_castsi128_si256': vector: t_Vec128
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_castsi128_si256 = mm256_castsi128_si256'

assume
val mm256_cvtepi16_epi32': vector: t_Vec128
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_cvtepi16_epi32 = mm256_cvtepi16_epi32'

assume
val mm256_packs_epi32': lhs: t_Vec256 -> rhs: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_packs_epi32 = mm256_packs_epi32'

assume
val mm256_inserti128_si256': v_CONTROL: i32 -> vector: t_Vec256 -> vector_i128: t_Vec128
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_inserti128_si256 (v_CONTROL: i32) = mm256_inserti128_si256' v_CONTROL

assume
val mm256_blend_epi16': v_CONTROL: i32 -> lhs: t_Vec256 -> rhs: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_blend_epi16 (v_CONTROL: i32) = mm256_blend_epi16' v_CONTROL

assume
val mm256_blend_epi32': v_CONTROL: i32 -> lhs: t_Vec256 -> rhs: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_blend_epi32 (v_CONTROL: i32) = mm256_blend_epi32' v_CONTROL

assume
val vec256_blendv_epi32': a: t_Vec256 -> b: t_Vec256 -> mask: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let vec256_blendv_epi32 = vec256_blendv_epi32'

assume
val mm256_srlv_epi32': vector: t_Vec256 -> counts: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_srlv_epi32 = mm256_srlv_epi32'

assume
val mm256_srlv_epi64': vector: t_Vec256 -> counts: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_srlv_epi64 = mm256_srlv_epi64'

assume
val mm_sllv_epi32': vector: t_Vec128 -> counts: t_Vec128
  -> Prims.Pure t_Vec128 Prims.l_True (fun _ -> Prims.l_True)

let mm_sllv_epi32 = mm_sllv_epi32'

assume
val mm256_slli_epi64': v_LEFT: i32 -> x: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_slli_epi64 (v_LEFT: i32) = mm256_slli_epi64' v_LEFT

assume
val mm256_bsrli_epi128': v_SHIFT_BY: i32 -> x: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_bsrli_epi128 (v_SHIFT_BY: i32) = mm256_bsrli_epi128' v_SHIFT_BY

assume
val mm256_andnot_si256': a: t_Vec256 -> b: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_andnot_si256 = mm256_andnot_si256'

assume
val mm256_set1_epi64x': a: i64 -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_set1_epi64x = mm256_set1_epi64x'

assume
val mm256_set_epi64x': input3: i64 -> input2: i64 -> input1: i64 -> input0: i64
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_set_epi64x = mm256_set_epi64x'

assume
val mm256_unpacklo_epi64': a: t_Vec256 -> b: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_unpacklo_epi64 = mm256_unpacklo_epi64'

assume
val mm256_permute2x128_si256': v_IMM8: i32 -> a: t_Vec256 -> b: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_permute2x128_si256 (v_IMM8: i32) = mm256_permute2x128_si256' v_IMM8
