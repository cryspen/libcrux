module Libcrux_intrinsics.Avx2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

unfold
let t_Vec128 = Core.Core_arch.X86.t____m128i

unfold
let t_Vec256 = Core.Core_arch.X86.t____m256i

val mm256_add_epi16 (lhs rhs: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_add_epi32 (lhs rhs: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_and_si256 (lhs rhs: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_andnot_si256 (a b: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_blend_epi16 (v_CONTROL: i32) (lhs rhs: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_castsi128_si256 (vector: Core.Core_arch.X86.t____m128i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_castsi256_si128 (vector: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m128i Prims.l_True (fun _ -> Prims.l_True)

val mm256_cmpgt_epi16 (lhs rhs: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_cvtepi16_epi32 (vector: Core.Core_arch.X86.t____m128i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_extracti128_si256 (v_CONTROL: i32) (vector: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m128i Prims.l_True (fun _ -> Prims.l_True)

val mm256_inserti128_si256
      (v_CONTROL: i32)
      (vector: Core.Core_arch.X86.t____m256i)
      (vector_i128: Core.Core_arch.X86.t____m128i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_loadu_si256_i16 (input: t_Slice i16)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_loadu_si256_u8 (input: t_Slice u8)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_madd_epi16 (lhs rhs: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_mul_epu32 (lhs rhs: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_mulhi_epi16 (lhs rhs: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_mullo_epi16 (lhs rhs: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_mullo_epi32 (lhs rhs: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_packs_epi32 (lhs rhs: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_permute2x128_si256 (v_IMM8: i32) (a b: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_permute4x64_epi64 (v_CONTROL: i32) (vector: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_permutevar8x32_epi32 (vector control: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_set1_epi16 (constant: i16)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_set1_epi32 (constant: i32)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_set1_epi64x (a: i64)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_set_epi16
      (input15 input14 input13 input12 input11 input10 input9 input8 input7 input6 input5 input4 input3 input2 input1 input0:
          i16)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_set_epi32 (input7 input6 input5 input4 input3 input2 input1 input0: i32)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_set_epi8
      (byte31 byte30 byte29 byte28 byte27 byte26 byte25 byte24 byte23 byte22 byte21 byte20 byte19 byte18 byte17 byte16 byte15 byte14 byte13 byte12 byte11 byte10 byte9 byte8 byte7 byte6 byte5 byte4 byte3 byte2 byte1 byte0:
          i8)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_setzero_si256: Prims.unit
  -> Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_shuffle_epi32 (v_CONTROL: i32) (vector: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_shuffle_epi8 (vector control: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_slli_epi16 (v_SHIFT_BY: i32) (vector: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_slli_epi32 (v_SHIFT_BY: i32) (vector: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_slli_epi64 (v_LEFT: i32) (x: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_sllv_epi32 (vector counts: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_srai_epi16 (v_SHIFT_BY: i32) (vector: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_srai_epi32 (v_SHIFT_BY: i32) (vector: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_srli_epi16 (v_SHIFT_BY: i32) (vector: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_srli_epi32 (v_SHIFT_BY: i32) (vector: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_srli_epi64 (v_SHIFT_BY: i32) (vector: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_storeu_si256_i16 (output: t_Slice i16) (vector: Core.Core_arch.X86.t____m256i)
    : Prims.Pure (t_Slice i16) Prims.l_True (fun _ -> Prims.l_True)

val mm256_storeu_si256_u8 (output: t_Slice u8) (vector: Core.Core_arch.X86.t____m256i)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

val mm256_sub_epi16 (lhs rhs: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_unpackhi_epi32 (lhs rhs: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_unpackhi_epi64 (lhs rhs: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_unpacklo_epi32 (lhs rhs: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_unpacklo_epi64 (a b: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm256_xor_si256 (lhs rhs: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mm_add_epi16 (lhs rhs: Core.Core_arch.X86.t____m128i)
    : Prims.Pure Core.Core_arch.X86.t____m128i Prims.l_True (fun _ -> Prims.l_True)

val mm_loadu_si128 (input: t_Slice u8)
    : Prims.Pure Core.Core_arch.X86.t____m128i Prims.l_True (fun _ -> Prims.l_True)

val mm_movemask_epi8 (vector: Core.Core_arch.X86.t____m128i)
    : Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

val mm_mulhi_epi16 (lhs rhs: Core.Core_arch.X86.t____m128i)
    : Prims.Pure Core.Core_arch.X86.t____m128i Prims.l_True (fun _ -> Prims.l_True)

val mm_mullo_epi16 (lhs rhs: Core.Core_arch.X86.t____m128i)
    : Prims.Pure Core.Core_arch.X86.t____m128i Prims.l_True (fun _ -> Prims.l_True)

val mm_packs_epi16 (lhs rhs: Core.Core_arch.X86.t____m128i)
    : Prims.Pure Core.Core_arch.X86.t____m128i Prims.l_True (fun _ -> Prims.l_True)

val mm_set1_epi16 (constant: i16)
    : Prims.Pure Core.Core_arch.X86.t____m128i Prims.l_True (fun _ -> Prims.l_True)

val mm_set_epi8
      (byte15 byte14 byte13 byte12 byte11 byte10 byte9 byte8 byte7 byte6 byte5 byte4 byte3 byte2 byte1 byte0:
          u8)
    : Prims.Pure Core.Core_arch.X86.t____m128i Prims.l_True (fun _ -> Prims.l_True)

val mm_shuffle_epi8 (vector control: Core.Core_arch.X86.t____m128i)
    : Prims.Pure Core.Core_arch.X86.t____m128i Prims.l_True (fun _ -> Prims.l_True)

val mm_storeu_bytes_si128 (output: t_Slice u8) (vector: Core.Core_arch.X86.t____m128i)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

val mm_storeu_si128 (output: t_Slice i16) (vector: Core.Core_arch.X86.t____m128i)
    : Prims.Pure (t_Slice i16) Prims.l_True (fun _ -> Prims.l_True)

val mm_sub_epi16 (lhs rhs: Core.Core_arch.X86.t____m128i)
    : Prims.Pure Core.Core_arch.X86.t____m128i Prims.l_True (fun _ -> Prims.l_True)
