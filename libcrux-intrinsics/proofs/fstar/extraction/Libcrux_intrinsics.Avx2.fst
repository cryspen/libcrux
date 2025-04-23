module Libcrux_intrinsics.Avx2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

assume
val mm256_storeu_si256_u8': output: t_Slice u8 -> vector: Minicore.Core_arch.X86.t_e_ee_m256i
  -> t_Slice u8

let mm256_storeu_si256_u8 = mm256_storeu_si256_u8'

assume
val mm256_storeu_si256_i16': output: t_Slice i16 -> vector: Minicore.Core_arch.X86.t_e_ee_m256i
  -> t_Slice i16

let mm256_storeu_si256_i16 = mm256_storeu_si256_i16'

assume
val mm256_storeu_si256_i32': output: t_Slice i32 -> vector: Minicore.Core_arch.X86.t_e_ee_m256i
  -> t_Slice i32

let mm256_storeu_si256_i32 = mm256_storeu_si256_i32'

assume
val mm_storeu_si128': output: t_Slice i16 -> vector: Minicore.Core_arch.X86.t_e_ee_m128i -> t_Slice i16

let mm_storeu_si128 = mm_storeu_si128'

assume
val mm_storeu_si128_i32': output: t_Slice i32 -> vector: Minicore.Core_arch.X86.t_e_ee_m128i
  -> t_Slice i32

let mm_storeu_si128_i32 = mm_storeu_si128_i32'

assume
val mm_storeu_bytes_si128': output: t_Slice u8 -> vector: Minicore.Core_arch.X86.t_e_ee_m128i
  -> Prims.Pure (t_Slice u8)
      Prims.l_True
      (ensures
        fun output_future ->
          let output_future:t_Slice u8 = output_future in
          (Core.Slice.impl__len #u8 output_future <: usize) =.
          (Core.Slice.impl__len #u8 output <: usize))

let mm_storeu_bytes_si128 = mm_storeu_bytes_si128'

assume
val mm_loadu_si128': input: t_Slice u8 -> Minicore.Core_arch.X86.t_e_ee_m128i

let mm_loadu_si128 = mm_loadu_si128'

assume
val mm256_loadu_si256_u8': input: t_Slice u8 -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_loadu_si256_u8 = mm256_loadu_si256_u8'

assume
val mm256_loadu_si256_i16': input: t_Slice i16 -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_loadu_si256_i16 = mm256_loadu_si256_i16'

assume
val mm256_loadu_si256_i32': input: t_Slice i32 -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_loadu_si256_i32 = mm256_loadu_si256_i32'

assume
val mm256_setzero_si256': Prims.unit -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_setzero_si256 = mm256_setzero_si256'

assume
val mm256_set_m128i': hi: Minicore.Core_arch.X86.t_e_ee_m128i -> lo: Minicore.Core_arch.X86.t_e_ee_m128i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_set_m128i = mm256_set_m128i'

let mm_set_epi8
      (byte15 byte14 byte13 byte12 byte11 byte10 byte9 byte8 byte7 byte6 byte5 byte4 byte3 byte2 byte1 byte0:
          u8)
    : Minicore.Core_arch.X86.t_e_ee_m128i =
  Minicore.Core_arch.X86.Sse2.e_mm_set_epi8 (cast (byte15 <: u8) <: i8) (cast (byte14 <: u8) <: i8)
    (cast (byte13 <: u8) <: i8) (cast (byte12 <: u8) <: i8) (cast (byte11 <: u8) <: i8)
    (cast (byte10 <: u8) <: i8) (cast (byte9 <: u8) <: i8) (cast (byte8 <: u8) <: i8)
    (cast (byte7 <: u8) <: i8) (cast (byte6 <: u8) <: i8) (cast (byte5 <: u8) <: i8)
    (cast (byte4 <: u8) <: i8) (cast (byte3 <: u8) <: i8) (cast (byte2 <: u8) <: i8)
    (cast (byte1 <: u8) <: i8) (cast (byte0 <: u8) <: i8)

let mm256_set_epi8
      (byte31 byte30 byte29 byte28 byte27 byte26 byte25 byte24 byte23 byte22 byte21 byte20 byte19 byte18 byte17 byte16 byte15 byte14 byte13 byte12 byte11 byte10 byte9 byte8 byte7 byte6 byte5 byte4 byte3 byte2 byte1 byte0:
          i8)
    : Minicore.Core_arch.X86.t_e_ee_m256i =
  Minicore.Core_arch.X86.Avx.e_mm256_set_epi8 byte31 byte30 byte29 byte28 byte27 byte26 byte25 byte24
    byte23 byte22 byte21 byte20 byte19 byte18 byte17 byte16 byte15 byte14 byte13 byte12 byte11
    byte10 byte9 byte8 byte7 byte6 byte5 byte4 byte3 byte2 byte1 byte0

assume
val mm256_set1_epi16': constant: i16 -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_set1_epi16 = mm256_set1_epi16'

let mm256_set_epi16
      (input15 input14 input13 input12 input11 input10 input9 input8 input7 input6 input5 input4 input3 input2 input1 input0:
          i16)
    : Minicore.Core_arch.X86.t_e_ee_m256i =
  Minicore.Core_arch.X86.Avx.e_mm256_set_epi16 input15 input14 input13 input12 input11 input10 input9
    input8 input7 input6 input5 input4 input3 input2 input1 input0

assume
val mm_set1_epi16': constant: i16 -> Minicore.Core_arch.X86.t_e_ee_m128i

let mm_set1_epi16 = mm_set1_epi16'

let mm256_set1_epi32 (constant: i32) : Minicore.Core_arch.X86.t_e_ee_m256i =
  Minicore.Core_arch.X86.Avx.e_mm256_set1_epi32 constant

assume
val mm_set_epi32': input3: i32 -> input2: i32 -> input1: i32 -> input0: i32
  -> Minicore.Core_arch.X86.t_e_ee_m128i

let mm_set_epi32 = mm_set_epi32'

let mm256_set_epi32 (input7 input6 input5 input4 input3 input2 input1 input0: i32)
    : Minicore.Core_arch.X86.t_e_ee_m256i =
  Minicore.Core_arch.X86.Avx.e_mm256_set_epi32 input7 input6 input5 input4 input3 input2 input1 input0

assume
val mm_add_epi16': lhs: Minicore.Core_arch.X86.t_e_ee_m128i -> rhs: Minicore.Core_arch.X86.t_e_ee_m128i
  -> Minicore.Core_arch.X86.t_e_ee_m128i

let mm_add_epi16 = mm_add_epi16'

assume
val mm256_add_epi16': lhs: Minicore.Core_arch.X86.t_e_ee_m256i -> rhs: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_add_epi16 = mm256_add_epi16'

assume
val mm256_madd_epi16': lhs: Minicore.Core_arch.X86.t_e_ee_m256i -> rhs: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_madd_epi16 = mm256_madd_epi16'

assume
val mm256_add_epi32': lhs: Minicore.Core_arch.X86.t_e_ee_m256i -> rhs: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_add_epi32 = mm256_add_epi32'

assume
val mm256_add_epi64': lhs: Minicore.Core_arch.X86.t_e_ee_m256i -> rhs: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_add_epi64 = mm256_add_epi64'

assume
val mm256_abs_epi32': a: Minicore.Core_arch.X86.t_e_ee_m256i -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_abs_epi32 = mm256_abs_epi32'

assume
val mm256_sub_epi16': lhs: Minicore.Core_arch.X86.t_e_ee_m256i -> rhs: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_sub_epi16 = mm256_sub_epi16'

let mm256_sub_epi32 (lhs rhs: Minicore.Core_arch.X86.t_e_ee_m256i) : Minicore.Core_arch.X86.t_e_ee_m256i =
  Minicore.Core_arch.X86.Avx2.e_mm256_sub_epi32 lhs rhs

assume
val mm_sub_epi16': lhs: Minicore.Core_arch.X86.t_e_ee_m128i -> rhs: Minicore.Core_arch.X86.t_e_ee_m128i
  -> Minicore.Core_arch.X86.t_e_ee_m128i

let mm_sub_epi16 = mm_sub_epi16'

let mm256_mullo_epi16 (lhs rhs: Minicore.Core_arch.X86.t_e_ee_m256i) : Minicore.Core_arch.X86.t_e_ee_m256i =
  Minicore.Core_arch.X86.Avx2.e_mm256_mullo_epi16 lhs rhs

let mm256_mullo_epi16_shifts
      (vector: Minicore.Core_arch.X86.t_e_ee_m256i)
      (s15 s14 s13 s12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0: u8)
    : Prims.Pure Minicore.Core_arch.X86.t_e_ee_m256i
      (requires
        s0 <. mk_u8 16 && s1 <. mk_u8 16 && s2 <. mk_u8 16 && s3 <. mk_u8 16 && s4 <. mk_u8 16 &&
        s5 <. mk_u8 16 &&
        s6 <. mk_u8 16 &&
        s7 <. mk_u8 16 &&
        s8 <. mk_u8 16 &&
        s9 <. mk_u8 16 &&
        s10 <. mk_u8 16 &&
        s11 <. mk_u8 16 &&
        s12 <. mk_u8 16 &&
        s13 <. mk_u8 16 &&
        s14 <. mk_u8 16 &&
        s15 <. mk_u8 16)
      (fun _ -> Prims.l_True) =
  mm256_mullo_epi16 vector
    (mm256_set_epi16 (mk_i16 1 <<! s15 <: i16) (mk_i16 1 <<! s14 <: i16) (mk_i16 1 <<! s13 <: i16)
        (mk_i16 1 <<! s12 <: i16) (mk_i16 1 <<! s11 <: i16) (mk_i16 1 <<! s10 <: i16)
        (mk_i16 1 <<! s9 <: i16) (mk_i16 1 <<! s8 <: i16) (mk_i16 1 <<! s7 <: i16)
        (mk_i16 1 <<! s6 <: i16) (mk_i16 1 <<! s5 <: i16) (mk_i16 1 <<! s4 <: i16)
        (mk_i16 1 <<! s3 <: i16) (mk_i16 1 <<! s2 <: i16) (mk_i16 1 <<! s1 <: i16)
        (mk_i16 1 <<! s0 <: i16)
      <:
      Minicore.Core_arch.X86.t_e_ee_m256i)

assume
val mm_mullo_epi16': lhs: Minicore.Core_arch.X86.t_e_ee_m128i -> rhs: Minicore.Core_arch.X86.t_e_ee_m128i
  -> Minicore.Core_arch.X86.t_e_ee_m128i

let mm_mullo_epi16 = mm_mullo_epi16'

assume
val mm256_cmpgt_epi16': lhs: Minicore.Core_arch.X86.t_e_ee_m256i -> rhs: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_cmpgt_epi16 = mm256_cmpgt_epi16'

assume
val mm256_cmpgt_epi32': lhs: Minicore.Core_arch.X86.t_e_ee_m256i -> rhs: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_cmpgt_epi32 = mm256_cmpgt_epi32'

assume
val mm256_cmpeq_epi32': a: Minicore.Core_arch.X86.t_e_ee_m256i -> b: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_cmpeq_epi32 = mm256_cmpeq_epi32'

assume
val mm256_sign_epi32': a: Minicore.Core_arch.X86.t_e_ee_m256i -> b: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_sign_epi32 = mm256_sign_epi32'

assume
val mm256_castsi256_ps': a: Minicore.Core_arch.X86.t_e_ee_m256i -> Minicore.Core_arch.X86.t_e_ee_m256

let mm256_castsi256_ps = mm256_castsi256_ps'

assume
val mm256_castps_si256': a: Minicore.Core_arch.X86.t_e_ee_m256 -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_castps_si256 = mm256_castps_si256'

assume
val mm256_movemask_ps': a: Minicore.Core_arch.X86.t_e_ee_m256 -> i32

let mm256_movemask_ps = mm256_movemask_ps'

assume
val mm_mulhi_epi16': lhs: Minicore.Core_arch.X86.t_e_ee_m128i -> rhs: Minicore.Core_arch.X86.t_e_ee_m128i
  -> Minicore.Core_arch.X86.t_e_ee_m128i

let mm_mulhi_epi16 = mm_mulhi_epi16'

assume
val mm256_mullo_epi32': lhs: Minicore.Core_arch.X86.t_e_ee_m256i -> rhs: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_mullo_epi32 = mm256_mullo_epi32'

assume
val mm256_mulhi_epi16': lhs: Minicore.Core_arch.X86.t_e_ee_m256i -> rhs: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_mulhi_epi16 = mm256_mulhi_epi16'

assume
val mm256_mul_epu32': lhs: Minicore.Core_arch.X86.t_e_ee_m256i -> rhs: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_mul_epu32 = mm256_mul_epu32'

let mm256_mul_epi32 (lhs rhs: Minicore.Core_arch.X86.t_e_ee_m256i) : Minicore.Core_arch.X86.t_e_ee_m256i =
  Minicore.Core_arch.X86.Avx2.e_mm256_mul_epi32 lhs rhs

assume
val mm256_and_si256': lhs: Minicore.Core_arch.X86.t_e_ee_m256i -> rhs: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_and_si256 = mm256_and_si256'

assume
val mm256_or_si256': a: Minicore.Core_arch.X86.t_e_ee_m256i -> b: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_or_si256 = mm256_or_si256'

assume
val mm256_testz_si256': lhs: Minicore.Core_arch.X86.t_e_ee_m256i -> rhs: Minicore.Core_arch.X86.t_e_ee_m256i
  -> i32

let mm256_testz_si256 = mm256_testz_si256'

assume
val mm256_xor_si256': lhs: Minicore.Core_arch.X86.t_e_ee_m256i -> rhs: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_xor_si256 = mm256_xor_si256'

assume
val mm256_srai_epi16': v_SHIFT_BY: i32 -> vector: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_srai_epi16 (v_SHIFT_BY: i32) = mm256_srai_epi16' v_SHIFT_BY

assume
val mm256_srai_epi32': v_SHIFT_BY: i32 -> vector: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_srai_epi32 (v_SHIFT_BY: i32) = mm256_srai_epi32' v_SHIFT_BY

assume
val mm256_srli_epi16': v_SHIFT_BY: i32 -> vector: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_srli_epi16 (v_SHIFT_BY: i32) = mm256_srli_epi16' v_SHIFT_BY

assume
val mm256_srli_epi32': v_SHIFT_BY: i32 -> vector: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_srli_epi32 (v_SHIFT_BY: i32) = mm256_srli_epi32' v_SHIFT_BY

assume
val mm_srli_epi64': v_SHIFT_BY: i32 -> vector: Minicore.Core_arch.X86.t_e_ee_m128i
  -> Minicore.Core_arch.X86.t_e_ee_m128i

let mm_srli_epi64 (v_SHIFT_BY: i32) = mm_srli_epi64' v_SHIFT_BY

let mm256_srli_epi64 (v_SHIFT_BY: i32) (vector: Minicore.Core_arch.X86.t_e_ee_m256i)
    : Prims.Pure Minicore.Core_arch.X86.t_e_ee_m256i
      (requires v_SHIFT_BY >. mk_i32 0 && v_SHIFT_BY <. mk_i32 64)
      (fun _ -> Prims.l_True) = Minicore.Core_arch.X86.Avx2.e_mm256_srli_epi64 v_SHIFT_BY vector

assume
val mm256_slli_epi16': v_SHIFT_BY: i32 -> vector: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_slli_epi16 (v_SHIFT_BY: i32) = mm256_slli_epi16' v_SHIFT_BY

assume
val mm256_slli_epi32': v_SHIFT_BY: i32 -> vector: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_slli_epi32 (v_SHIFT_BY: i32) = mm256_slli_epi32' v_SHIFT_BY

let mm_shuffle_epi8 (vector control: Minicore.Core_arch.X86.t_e_ee_m128i)
    : Minicore.Core_arch.X86.t_e_ee_m128i = Minicore.Core_arch.X86.Ssse3.e_mm_shuffle_epi8 vector control

let mm256_shuffle_epi8 (vector control: Minicore.Core_arch.X86.t_e_ee_m256i)
    : Minicore.Core_arch.X86.t_e_ee_m256i = Minicore.Core_arch.X86.Avx2.e_mm256_shuffle_epi8 vector control

let mm256_shuffle_epi32 (v_CONTROL: i32) (vector: Minicore.Core_arch.X86.t_e_ee_m256i)
    : Minicore.Core_arch.X86.t_e_ee_m256i =
  Minicore.Core_arch.X86.Avx2.e_mm256_shuffle_epi32 v_CONTROL vector

assume
val mm256_permute4x64_epi64': v_CONTROL: i32 -> vector: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_permute4x64_epi64 (v_CONTROL: i32) = mm256_permute4x64_epi64' v_CONTROL

assume
val mm256_unpackhi_epi64':
    lhs: Minicore.Core_arch.X86.t_e_ee_m256i ->
    rhs: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_unpackhi_epi64 = mm256_unpackhi_epi64'

assume
val mm256_unpacklo_epi32':
    lhs: Minicore.Core_arch.X86.t_e_ee_m256i ->
    rhs: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_unpacklo_epi32 = mm256_unpacklo_epi32'

assume
val mm256_unpackhi_epi32':
    lhs: Minicore.Core_arch.X86.t_e_ee_m256i ->
    rhs: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_unpackhi_epi32 = mm256_unpackhi_epi32'

let mm256_castsi256_si128 (vector: Minicore.Core_arch.X86.t_e_ee_m256i)
    : Minicore.Core_arch.X86.t_e_ee_m128i = Minicore.Core_arch.X86.Avx.e_mm256_castsi256_si128 vector

assume
val mm256_castsi128_si256': vector: Minicore.Core_arch.X86.t_e_ee_m128i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_castsi128_si256 = mm256_castsi128_si256'

assume
val mm256_cvtepi16_epi32': vector: Minicore.Core_arch.X86.t_e_ee_m128i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_cvtepi16_epi32 = mm256_cvtepi16_epi32'

assume
val mm_packs_epi16': lhs: Minicore.Core_arch.X86.t_e_ee_m128i -> rhs: Minicore.Core_arch.X86.t_e_ee_m128i
  -> Minicore.Core_arch.X86.t_e_ee_m128i

let mm_packs_epi16 = mm_packs_epi16'

assume
val mm256_packs_epi32': lhs: Minicore.Core_arch.X86.t_e_ee_m256i -> rhs: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_packs_epi32 = mm256_packs_epi32'

let mm256_extracti128_si256 (v_CONTROL: i32) (vector: Minicore.Core_arch.X86.t_e_ee_m256i)
    : Minicore.Core_arch.X86.t_e_ee_m128i =
  Minicore.Core_arch.X86.Avx2.e_mm256_extracti128_si256 v_CONTROL vector

assume
val mm256_inserti128_si256':
    v_CONTROL: i32 ->
    vector: Minicore.Core_arch.X86.t_e_ee_m256i ->
    vector_i128: Minicore.Core_arch.X86.t_e_ee_m128i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_inserti128_si256 (v_CONTROL: i32) = mm256_inserti128_si256' v_CONTROL

assume
val mm256_blend_epi16':
    v_CONTROL: i32 ->
    lhs: Minicore.Core_arch.X86.t_e_ee_m256i ->
    rhs: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_blend_epi16 (v_CONTROL: i32) = mm256_blend_epi16' v_CONTROL

let mm256_blend_epi32 (v_CONTROL: i32) (lhs rhs: Minicore.Core_arch.X86.t_e_ee_m256i)
    : Minicore.Core_arch.X86.t_e_ee_m256i =
  Minicore.Core_arch.X86.Avx2.e_mm256_blend_epi32 v_CONTROL lhs rhs

assume
val vec256_blendv_epi32':
    a: Minicore.Core_arch.X86.t_e_ee_m256i ->
    b: Minicore.Core_arch.X86.t_e_ee_m256i ->
    mask: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let vec256_blendv_epi32 = vec256_blendv_epi32'

assume
val mm_movemask_epi8': vector: Minicore.Core_arch.X86.t_e_ee_m128i -> i32

let mm_movemask_epi8 = mm_movemask_epi8'

let mm256_permutevar8x32_epi32 (vector control: Minicore.Core_arch.X86.t_e_ee_m256i)
    : Minicore.Core_arch.X86.t_e_ee_m256i =
  Minicore.Core_arch.X86.Avx2.e_mm256_permutevar8x32_epi32 vector control

let mm256_srlv_epi32 (vector counts: Minicore.Core_arch.X86.t_e_ee_m256i)
    : Minicore.Core_arch.X86.t_e_ee_m256i = Minicore.Core_arch.X86.Avx2.e_mm256_srlv_epi32 vector counts

assume
val mm256_srlv_epi64':
    vector: Minicore.Core_arch.X86.t_e_ee_m256i ->
    counts: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_srlv_epi64 = mm256_srlv_epi64'

assume
val mm_sllv_epi32':
    vector: Minicore.Core_arch.X86.t_e_ee_m128i ->
    counts: Minicore.Core_arch.X86.t_e_ee_m128i
  -> Minicore.Core_arch.X86.t_e_ee_m128i

let mm_sllv_epi32 = mm_sllv_epi32'

let mm256_sllv_epi32 (vector counts: Minicore.Core_arch.X86.t_e_ee_m256i)
    : Minicore.Core_arch.X86.t_e_ee_m256i = Minicore.Core_arch.X86.Avx2.e_mm256_sllv_epi32 vector counts

assume
val mm256_slli_epi64': v_LEFT: i32 -> x: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_slli_epi64 (v_LEFT: i32) = mm256_slli_epi64' v_LEFT

assume
val mm256_bsrli_epi128': v_SHIFT_BY: i32 -> x: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_bsrli_epi128 (v_SHIFT_BY: i32) = mm256_bsrli_epi128' v_SHIFT_BY

assume
val mm256_andnot_si256': a: Minicore.Core_arch.X86.t_e_ee_m256i -> b: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_andnot_si256 = mm256_andnot_si256'

assume
val mm256_set1_epi64x': a: i64 -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_set1_epi64x = mm256_set1_epi64x'

assume
val mm256_set_epi64x': input3: i64 -> input2: i64 -> input1: i64 -> input0: i64
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_set_epi64x = mm256_set_epi64x'

assume
val mm256_unpacklo_epi64':
    lhs: Minicore.Core_arch.X86.t_e_ee_m256i ->
    rhs: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_unpacklo_epi64 = mm256_unpacklo_epi64'

assume
val mm256_permute2x128_si256':
    v_IMM8: i32 ->
    a: Minicore.Core_arch.X86.t_e_ee_m256i ->
    b: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Minicore.Core_arch.X86.t_e_ee_m256i

let mm256_permute2x128_si256 (v_IMM8: i32) = mm256_permute2x128_si256' v_IMM8
