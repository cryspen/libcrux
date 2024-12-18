module Libcrux_intrinsics.Avx2_extract
<<<<<<< HEAD
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
=======
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
>>>>>>> main
open Core
open FStar.Mul

assume
<<<<<<< HEAD
val mm256_abs_epi32': a: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm256_abs_epi32 = mm256_abs_epi32'

assume
val mm256_add_epi16': lhs: u8 -> rhs: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm256_add_epi16 = mm256_add_epi16'

assume
val mm256_add_epi32': lhs: u8 -> rhs: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm256_add_epi32 = mm256_add_epi32'

assume
val mm256_add_epi64': lhs: u8 -> rhs: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm256_add_epi64 = mm256_add_epi64'

assume
val mm256_and_si256': lhs: u8 -> rhs: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm256_and_si256 = mm256_and_si256'

assume
val mm256_andnot_si256': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm256_andnot_si256 = mm256_andnot_si256'

assume
val mm256_blend_epi16': v_CONTROL: i32 -> lhs: u8 -> rhs: u8
  -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm256_blend_epi16 (v_CONTROL: i32) = mm256_blend_epi16' v_CONTROL

assume
val mm256_blend_epi32': v_CONTROL: i32 -> lhs: u8 -> rhs: u8
  -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm256_blend_epi32 (v_CONTROL: i32) = mm256_blend_epi32' v_CONTROL

assume
val mm256_bsrli_epi128': v_SHIFT_BY: i32 -> x: u8
  -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm256_bsrli_epi128 (v_SHIFT_BY: i32) = mm256_bsrli_epi128' v_SHIFT_BY

assume
val mm256_castsi128_si256': vector: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm256_castsi128_si256 = mm256_castsi128_si256'

assume
val mm256_castsi256_ps': a: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm256_castsi256_ps = mm256_castsi256_ps'

assume
val mm256_castsi256_si128': vector: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm256_castsi256_si128 = mm256_castsi256_si128'

assume
val mm256_cmpeq_epi32': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm256_cmpeq_epi32 = mm256_cmpeq_epi32'

assume
val mm256_cmpgt_epi16': lhs: u8 -> rhs: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm256_cmpgt_epi16 = mm256_cmpgt_epi16'

assume
val mm256_cmpgt_epi32': lhs: u8 -> rhs: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm256_cmpgt_epi32 = mm256_cmpgt_epi32'

assume
val mm256_cvtepi16_epi32': vector: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm256_cvtepi16_epi32 = mm256_cvtepi16_epi32'

assume
val mm256_extracti128_si256': v_CONTROL: i32 -> vector: u8
  -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm256_extracti128_si256 (v_CONTROL: i32) = mm256_extracti128_si256' v_CONTROL

assume
val mm256_inserti128_si256': v_CONTROL: i32 -> vector: u8 -> vector_i128: u8
  -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm256_inserti128_si256 (v_CONTROL: i32) = mm256_inserti128_si256' v_CONTROL

assume
val mm256_loadu_si256_i16': input: t_Slice i16 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm256_loadu_si256_i16 = mm256_loadu_si256_i16'

assume
val mm256_loadu_si256_i32': input: t_Slice i32 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm256_loadu_si256_i32 = mm256_loadu_si256_i32'

assume
val mm256_loadu_si256_u8': input: t_Slice u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm256_loadu_si256_u8 = mm256_loadu_si256_u8'

assume
val mm256_madd_epi16': lhs: u8 -> rhs: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm256_madd_epi16 = mm256_madd_epi16'

assume
=======
>>>>>>> main
val mm256_movemask_ps': a: u8 -> Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

let mm256_movemask_ps = mm256_movemask_ps'

<<<<<<< HEAD
assume
val mm256_mul_epi32': lhs: u8 -> rhs: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': Core.Clone.t_Clone t_Vec128

let impl_3 = impl_3'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': Core.Marker.t_Copy t_Vec128

let impl_2 = impl_2'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl': Core.Clone.t_Clone t_Vec256

let impl = impl'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Core.Marker.t_Copy t_Vec256

let impl_1 = impl_1'

assume
val mm256_abs_epi32': a: t_Vec256 -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_abs_epi32 = mm256_abs_epi32'

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
val mm256_add_epi64': lhs: t_Vec256 -> rhs: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_add_epi64 = mm256_add_epi64'

assume
val mm256_andnot_si256': a: t_Vec256 -> b: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_andnot_si256 = mm256_andnot_si256'

assume
val mm256_blend_epi16': v_CONTROL: i32 -> lhs: t_Vec256 -> rhs: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_blend_epi16 (v_CONTROL: i32) = mm256_blend_epi16' v_CONTROL

assume
val mm256_blend_epi32': v_CONTROL: i32 -> lhs: t_Vec256 -> rhs: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_blend_epi32 (v_CONTROL: i32) = mm256_blend_epi32' v_CONTROL

assume
val mm256_bsrli_epi128': v_SHIFT_BY: i32 -> x: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_bsrli_epi128 (v_SHIFT_BY: i32) = mm256_bsrli_epi128' v_SHIFT_BY

assume
val mm256_castsi128_si256': vector: t_Vec128
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_castsi128_si256 = mm256_castsi128_si256'

assume
val mm256_castsi256_ps': a: t_Vec256 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm256_castsi256_ps = mm256_castsi256_ps'

assume
val mm256_cmpeq_epi32': a: t_Vec256 -> b: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_cmpeq_epi32 = mm256_cmpeq_epi32'

assume
val mm256_cmpgt_epi16': lhs: t_Vec256 -> rhs: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_cmpgt_epi16 = mm256_cmpgt_epi16'

assume
val mm256_cmpgt_epi32': lhs: t_Vec256 -> rhs: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_cmpgt_epi32 = mm256_cmpgt_epi32'

assume
val mm256_cvtepi16_epi32': vector: t_Vec128
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_cvtepi16_epi32 = mm256_cvtepi16_epi32'

assume
val mm256_inserti128_si256': v_CONTROL: i32 -> vector: t_Vec256 -> vector_i128: t_Vec128
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_inserti128_si256 (v_CONTROL: i32) = mm256_inserti128_si256' v_CONTROL

assume
val mm256_loadu_si256_i16': input: t_Slice i16
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_loadu_si256_i16 = mm256_loadu_si256_i16'

assume
val mm256_loadu_si256_i32': input: t_Slice i32
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_loadu_si256_i32 = mm256_loadu_si256_i32'

assume
val mm256_loadu_si256_u8': input: t_Slice u8
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

let mm256_loadu_si256_u8 = mm256_loadu_si256_u8'

assume
val mm256_mul_epi32': lhs: t_Vec256 -> rhs: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)
>>>>>>> main

let mm256_mul_epi32 = mm256_mul_epi32'

assume
<<<<<<< HEAD
val mm256_mul_epu32': lhs: u8 -> rhs: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
val mm256_mul_epu32': lhs: t_Vec256 -> rhs: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)
>>>>>>> main

let mm256_mul_epu32 = mm256_mul_epu32'

assume
<<<<<<< HEAD
val mm256_mulhi_epi16': lhs: u8 -> rhs: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
val mm256_mulhi_epi16': lhs: t_Vec256 -> rhs: t_Vec256
  -> Prims.Pure t_Vec256
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Vec256 = result in
          vec256_as_i16x16 result ==
          Spec.Utils.map2 (fun x y -> cast (((cast x <: i32) *. (cast y <: i32)) >>! 16l) <: i16)
            (vec256_as_i16x16 lhs)
            (vec256_as_i16x16 rhs))
>>>>>>> main

let mm256_mulhi_epi16 = mm256_mulhi_epi16'

assume
<<<<<<< HEAD
val mm256_mullo_epi16': lhs: u8 -> rhs: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm256_mullo_epi16 = mm256_mullo_epi16'

assume
val mm256_mullo_epi32': lhs: u8 -> rhs: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
val mm256_mullo_epi32': lhs: t_Vec256 -> rhs: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)
>>>>>>> main

let mm256_mullo_epi32 = mm256_mullo_epi32'

assume
<<<<<<< HEAD
val mm256_or_si256': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
val mm256_or_si256': a: t_Vec256 -> b: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)
>>>>>>> main

let mm256_or_si256 = mm256_or_si256'

assume
<<<<<<< HEAD
val mm256_packs_epi32': lhs: u8 -> rhs: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
val mm256_packs_epi32': lhs: t_Vec256 -> rhs: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)
>>>>>>> main

let mm256_packs_epi32 = mm256_packs_epi32'

assume
<<<<<<< HEAD
val mm256_permute2x128_si256': v_IMM8: i32 -> a: u8 -> b: u8
  -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
val mm256_permute2x128_si256': v_IMM8: i32 -> a: t_Vec256 -> b: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)
>>>>>>> main

let mm256_permute2x128_si256 (v_IMM8: i32) = mm256_permute2x128_si256' v_IMM8

assume
<<<<<<< HEAD
val mm256_permute4x64_epi64': v_CONTROL: i32 -> vector: u8
  -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
val mm256_permute4x64_epi64': v_CONTROL: i32 -> vector: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)
>>>>>>> main

let mm256_permute4x64_epi64 (v_CONTROL: i32) = mm256_permute4x64_epi64' v_CONTROL

assume
<<<<<<< HEAD
val mm256_permutevar8x32_epi32': vector: u8 -> control: u8
  -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm256_permutevar8x32_epi32 = mm256_permutevar8x32_epi32'

assume
val mm256_set1_epi16': constant: i16 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm256_set1_epi16 = mm256_set1_epi16'

assume
val mm256_set1_epi32': constant: i32 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
val mm256_set1_epi32': constant: i32 -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)
>>>>>>> main

let mm256_set1_epi32 = mm256_set1_epi32'

assume
<<<<<<< HEAD
val mm256_set1_epi64x': a: i64 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
val mm256_set1_epi64x': a: i64 -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)
>>>>>>> main

let mm256_set1_epi64x = mm256_set1_epi64x'

assume
<<<<<<< HEAD
val mm256_set_epi16':
    input15: i16 ->
    input14: i16 ->
    input13: i16 ->
    input12: i16 ->
    input11: i16 ->
    input10: i16 ->
    input9: i16 ->
    input8: i16 ->
    input7: i16 ->
    input6: i16 ->
    input5: i16 ->
    input4: i16 ->
    input3: i16 ->
    input2: i16 ->
    input1: i16 ->
    input0: i16
  -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm256_set_epi16 = mm256_set_epi16'

assume
val mm256_set_epi32':
    input7: i32 ->
    input6: i32 ->
    input5: i32 ->
    input4: i32 ->
    input3: i32 ->
    input2: i32 ->
    input1: i32 ->
    input0: i32
  -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm256_set_epi32 = mm256_set_epi32'

assume
val mm256_set_epi64x': input3: i64 -> input2: i64 -> input1: i64 -> input0: i64
  -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
val mm256_set_epi64x': input3: i64 -> input2: i64 -> input1: i64 -> input0: i64
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)
>>>>>>> main

let mm256_set_epi64x = mm256_set_epi64x'

assume
<<<<<<< HEAD
val mm256_set_epi8':
    byte31: i8 ->
    byte30: i8 ->
    byte29: i8 ->
    byte28: i8 ->
    byte27: i8 ->
    byte26: i8 ->
    byte25: i8 ->
    byte24: i8 ->
    byte23: i8 ->
    byte22: i8 ->
    byte21: i8 ->
    byte20: i8 ->
    byte19: i8 ->
    byte18: i8 ->
    byte17: i8 ->
    byte16: i8 ->
    byte15: i8 ->
    byte14: i8 ->
    byte13: i8 ->
    byte12: i8 ->
    byte11: i8 ->
    byte10: i8 ->
    byte9: i8 ->
    byte8: i8 ->
    byte7: i8 ->
    byte6: i8 ->
    byte5: i8 ->
    byte4: i8 ->
    byte3: i8 ->
    byte2: i8 ->
    byte1: i8 ->
    byte0: i8
  -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm256_set_epi8 = mm256_set_epi8'

assume
val mm256_set_m128i': hi: u8 -> lo: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
val mm256_set_m128i': hi: t_Vec128 -> lo: t_Vec128
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)
>>>>>>> main

let mm256_set_m128i = mm256_set_m128i'

assume
<<<<<<< HEAD
val mm256_setzero_si256': Prims.unit -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
val mm256_setzero_si256': Prims.unit -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)
>>>>>>> main

let mm256_setzero_si256 = mm256_setzero_si256'

assume
<<<<<<< HEAD
val mm256_shuffle_epi32': v_CONTROL: i32 -> vector: u8
  -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
val mm256_shuffle_epi32': v_CONTROL: i32 -> vector: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)
>>>>>>> main

let mm256_shuffle_epi32 (v_CONTROL: i32) = mm256_shuffle_epi32' v_CONTROL

assume
<<<<<<< HEAD
val mm256_shuffle_epi8': vector: u8 -> control: u8
  -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm256_shuffle_epi8 = mm256_shuffle_epi8'

assume
val mm256_sign_epi32': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
val mm256_sign_epi32': a: t_Vec256 -> b: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)
>>>>>>> main

let mm256_sign_epi32 = mm256_sign_epi32'

assume
<<<<<<< HEAD
val mm256_slli_epi16': v_SHIFT_BY: i32 -> vector: u8
  -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm256_slli_epi16 (v_SHIFT_BY: i32) = mm256_slli_epi16' v_SHIFT_BY

assume
val mm256_slli_epi32': v_SHIFT_BY: i32 -> vector: u8
  -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
val mm256_slli_epi32': v_SHIFT_BY: i32 -> vector: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)
>>>>>>> main

let mm256_slli_epi32 (v_SHIFT_BY: i32) = mm256_slli_epi32' v_SHIFT_BY

assume
<<<<<<< HEAD
val mm256_slli_epi64': v_LEFT: i32 -> x: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
val mm256_slli_epi64': v_LEFT: i32 -> x: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)
>>>>>>> main

let mm256_slli_epi64 (v_LEFT: i32) = mm256_slli_epi64' v_LEFT

assume
<<<<<<< HEAD
val mm256_sllv_epi32': vector: u8 -> counts: u8
  -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm256_sllv_epi32 = mm256_sllv_epi32'

assume
val mm256_srai_epi16': v_SHIFT_BY: i32 -> vector: u8
  -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
val mm256_srai_epi16': v_SHIFT_BY: i32 -> vector: t_Vec256
  -> Prims.Pure t_Vec256
      (requires v_SHIFT_BY >=. 0l && v_SHIFT_BY <. 16l)
      (ensures
        fun result ->
          let result:t_Vec256 = result in
          vec256_as_i16x16 result ==
          Spec.Utils.map_array (fun x -> x >>! v_SHIFT_BY) (vec256_as_i16x16 vector))
>>>>>>> main

let mm256_srai_epi16 (v_SHIFT_BY: i32) = mm256_srai_epi16' v_SHIFT_BY

assume
<<<<<<< HEAD
val mm256_srai_epi32': v_SHIFT_BY: i32 -> vector: u8
  -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
val mm256_srai_epi32': v_SHIFT_BY: i32 -> vector: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)
>>>>>>> main

let mm256_srai_epi32 (v_SHIFT_BY: i32) = mm256_srai_epi32' v_SHIFT_BY

assume
<<<<<<< HEAD
val mm256_srli_epi16': v_SHIFT_BY: i32 -> vector: u8
  -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm256_srli_epi16 (v_SHIFT_BY: i32) = mm256_srli_epi16' v_SHIFT_BY

assume
val mm256_srli_epi32': v_SHIFT_BY: i32 -> vector: u8
  -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
val mm256_srli_epi32': v_SHIFT_BY: i32 -> vector: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)
>>>>>>> main

let mm256_srli_epi32 (v_SHIFT_BY: i32) = mm256_srli_epi32' v_SHIFT_BY

assume
<<<<<<< HEAD
val mm256_srli_epi64': v_SHIFT_BY: i32 -> vector: u8
  -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm256_srli_epi64 (v_SHIFT_BY: i32) = mm256_srli_epi64' v_SHIFT_BY

assume
val mm256_srlv_epi32': vector: u8 -> counts: u8
  -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
val mm256_srlv_epi32': vector: t_Vec256 -> counts: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)
>>>>>>> main

let mm256_srlv_epi32 = mm256_srlv_epi32'

assume
<<<<<<< HEAD
val mm256_srlv_epi64': vector: u8 -> counts: u8
  -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
val mm256_srlv_epi64': vector: t_Vec256 -> counts: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)
>>>>>>> main

let mm256_srlv_epi64 = mm256_srlv_epi64'

assume
<<<<<<< HEAD
val mm256_storeu_si256_i16': output: t_Slice i16 -> vector: u8
  -> Prims.Pure (t_Slice i16) Prims.l_True (fun _ -> Prims.l_True)
=======
val mm256_storeu_si256_i16': output: t_Slice i16 -> vector: t_Vec256
  -> Prims.Pure (t_Slice i16)
      Prims.l_True
      (ensures
        fun output_future ->
          let output_future:t_Slice i16 = output_future in
          (Core.Slice.impl__len #i16 output_future <: usize) =.
          (Core.Slice.impl__len #i16 output <: usize))
>>>>>>> main

let mm256_storeu_si256_i16 = mm256_storeu_si256_i16'

assume
<<<<<<< HEAD
val mm256_storeu_si256_i32': output: t_Slice i32 -> vector: u8
=======
val mm256_storeu_si256_i32': output: t_Slice i32 -> vector: t_Vec256
>>>>>>> main
  -> Prims.Pure (t_Slice i32) Prims.l_True (fun _ -> Prims.l_True)

let mm256_storeu_si256_i32 = mm256_storeu_si256_i32'

assume
<<<<<<< HEAD
val mm256_storeu_si256_u8': output: t_Slice u8 -> vector: u8
=======
val mm256_storeu_si256_u8': output: t_Slice u8 -> vector: t_Vec256
>>>>>>> main
  -> Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

let mm256_storeu_si256_u8 = mm256_storeu_si256_u8'

assume
<<<<<<< HEAD
val mm256_sub_epi16': lhs: u8 -> rhs: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
val mm256_sub_epi16': lhs: t_Vec256 -> rhs: t_Vec256
  -> Prims.Pure t_Vec256
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Vec256 = result in
          vec256_as_i16x16 result ==
          Spec.Utils.map2 ( -. ) (vec256_as_i16x16 lhs) (vec256_as_i16x16 rhs))
>>>>>>> main

let mm256_sub_epi16 = mm256_sub_epi16'

assume
<<<<<<< HEAD
val mm256_sub_epi32': lhs: u8 -> rhs: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
val mm256_sub_epi32': lhs: t_Vec256 -> rhs: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)
>>>>>>> main

let mm256_sub_epi32 = mm256_sub_epi32'

assume
<<<<<<< HEAD
val mm256_testz_si256': lhs: u8 -> rhs: u8 -> Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)
=======
val mm256_testz_si256': lhs: t_Vec256 -> rhs: t_Vec256
  -> Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)
>>>>>>> main

let mm256_testz_si256 = mm256_testz_si256'

assume
<<<<<<< HEAD
val mm256_unpackhi_epi32': lhs: u8 -> rhs: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
val mm256_unpackhi_epi32': lhs: t_Vec256 -> rhs: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)
>>>>>>> main

let mm256_unpackhi_epi32 = mm256_unpackhi_epi32'

assume
<<<<<<< HEAD
val mm256_unpackhi_epi64': lhs: u8 -> rhs: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
val mm256_unpackhi_epi64': lhs: t_Vec256 -> rhs: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)
>>>>>>> main

let mm256_unpackhi_epi64 = mm256_unpackhi_epi64'

assume
<<<<<<< HEAD
val mm256_unpacklo_epi32': lhs: u8 -> rhs: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
val mm256_unpacklo_epi32': lhs: t_Vec256 -> rhs: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)
>>>>>>> main

let mm256_unpacklo_epi32 = mm256_unpacklo_epi32'

assume
<<<<<<< HEAD
val mm256_unpacklo_epi64': a: u8 -> b: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
val mm256_unpacklo_epi64': a: t_Vec256 -> b: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)
>>>>>>> main

let mm256_unpacklo_epi64 = mm256_unpacklo_epi64'

assume
<<<<<<< HEAD
val mm256_xor_si256': lhs: u8 -> rhs: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
val mm256_xor_si256': lhs: t_Vec256 -> rhs: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)
>>>>>>> main

let mm256_xor_si256 = mm256_xor_si256'

assume
<<<<<<< HEAD
val mm_add_epi16': lhs: u8 -> rhs: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
val mm_add_epi16': lhs: t_Vec128 -> rhs: t_Vec128
  -> Prims.Pure t_Vec128
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Vec128 = result in
          vec128_as_i16x8 result ==
          Spec.Utils.map2 ( +. ) (vec128_as_i16x8 lhs) (vec128_as_i16x8 rhs))
>>>>>>> main

let mm_add_epi16 = mm_add_epi16'

assume
<<<<<<< HEAD
val mm_loadu_si128': input: t_Slice u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm_loadu_si128 = mm_loadu_si128'

assume
val mm_movemask_epi8': vector: u8 -> Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

let mm_movemask_epi8 = mm_movemask_epi8'

assume
val mm_mulhi_epi16': lhs: u8 -> rhs: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
val mm_mulhi_epi16': lhs: t_Vec128 -> rhs: t_Vec128
  -> Prims.Pure t_Vec128
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Vec128 = result in
          vec128_as_i16x8 result ==
          Spec.Utils.map2 (fun x y -> cast (((cast x <: i32) *. (cast y <: i32)) >>! 16l) <: i16)
            (vec128_as_i16x8 lhs)
            (vec128_as_i16x8 rhs))
>>>>>>> main

let mm_mulhi_epi16 = mm_mulhi_epi16'

assume
<<<<<<< HEAD
val mm_mullo_epi16': lhs: u8 -> rhs: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
val mm_mullo_epi16': lhs: t_Vec128 -> rhs: t_Vec128
  -> Prims.Pure t_Vec128
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Vec128 = result in
          vec128_as_i16x8 result ==
          Spec.Utils.map2 mul_mod (vec128_as_i16x8 lhs) (vec128_as_i16x8 rhs))
>>>>>>> main

let mm_mullo_epi16 = mm_mullo_epi16'

assume
<<<<<<< HEAD
val mm_packs_epi16': lhs: u8 -> rhs: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm_packs_epi16 = mm_packs_epi16'

assume
val mm_set1_epi16': constant: i16 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
val mm_set1_epi16': constant: i16
  -> Prims.Pure t_Vec128
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Vec128 = result in
          vec128_as_i16x8 result == Spec.Utils.create (sz 8) constant)
>>>>>>> main

let mm_set1_epi16 = mm_set1_epi16'

assume
val mm_set_epi32': input3: i32 -> input2: i32 -> input1: i32 -> input0: i32
<<<<<<< HEAD
  -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
  -> Prims.Pure t_Vec128 Prims.l_True (fun _ -> Prims.l_True)
>>>>>>> main

let mm_set_epi32 = mm_set_epi32'

assume
<<<<<<< HEAD
val mm_set_epi8':
    byte15: u8 ->
    byte14: u8 ->
    byte13: u8 ->
    byte12: u8 ->
    byte11: u8 ->
    byte10: u8 ->
    byte9: u8 ->
    byte8: u8 ->
    byte7: u8 ->
    byte6: u8 ->
    byte5: u8 ->
    byte4: u8 ->
    byte3: u8 ->
    byte2: u8 ->
    byte1: u8 ->
    byte0: u8
  -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm_set_epi8 = mm_set_epi8'

assume
val mm_shuffle_epi8': vector: u8 -> control: u8
  -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let mm_shuffle_epi8 = mm_shuffle_epi8'

assume
val mm_sllv_epi32': vector: u8 -> counts: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
val mm_sllv_epi32': vector: t_Vec128 -> counts: t_Vec128
  -> Prims.Pure t_Vec128 Prims.l_True (fun _ -> Prims.l_True)
>>>>>>> main

let mm_sllv_epi32 = mm_sllv_epi32'

assume
<<<<<<< HEAD
val mm_srli_epi64': v_SHIFT_BY: i32 -> vector: u8
  -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
val mm_srli_epi64': v_SHIFT_BY: i32 -> vector: t_Vec128
  -> Prims.Pure t_Vec128 Prims.l_True (fun _ -> Prims.l_True)
>>>>>>> main

let mm_srli_epi64 (v_SHIFT_BY: i32) = mm_srli_epi64' v_SHIFT_BY

assume
<<<<<<< HEAD
val mm_storeu_bytes_si128': output: t_Slice u8 -> vector: u8
  -> Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

let mm_storeu_bytes_si128 = mm_storeu_bytes_si128'

assume
val mm_storeu_si128': output: t_Slice i16 -> vector: u8
=======
val mm_storeu_si128': output: t_Slice i16 -> vector: t_Vec128
>>>>>>> main
  -> Prims.Pure (t_Slice i16) Prims.l_True (fun _ -> Prims.l_True)

let mm_storeu_si128 = mm_storeu_si128'

assume
<<<<<<< HEAD
val mm_storeu_si128_i32': output: t_Slice i32 -> vector: u8
=======
val mm_storeu_si128_i32': output: t_Slice i32 -> vector: t_Vec128
>>>>>>> main
  -> Prims.Pure (t_Slice i32) Prims.l_True (fun _ -> Prims.l_True)

let mm_storeu_si128_i32 = mm_storeu_si128_i32'

assume
<<<<<<< HEAD
val mm_sub_epi16': lhs: u8 -> rhs: u8 -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
val mm_sub_epi16': lhs: t_Vec128 -> rhs: t_Vec128
  -> Prims.Pure t_Vec128
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Vec128 = result in
          vec128_as_i16x8 result ==
          Spec.Utils.map2 ( -. ) (vec128_as_i16x8 lhs) (vec128_as_i16x8 rhs))
>>>>>>> main

let mm_sub_epi16 = mm_sub_epi16'

assume
<<<<<<< HEAD
val vec256_blendv_epi32': a: u8 -> b: u8 -> mask: u8
  -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
=======
val vec256_blendv_epi32': a: t_Vec256 -> b: t_Vec256 -> mask: t_Vec256
  -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)
>>>>>>> main

let vec256_blendv_epi32 = vec256_blendv_epi32'
