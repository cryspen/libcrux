module Libcrux_intrinsics.Avx2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

assume
val mm256_storeu_si256_u8':
    output: t_Slice u8 ->
    vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> t_Slice u8

unfold
let mm256_storeu_si256_u8 = mm256_storeu_si256_u8'

assume
val mm256_storeu_si256_i16':
    output: t_Slice i16 ->
    vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> t_Slice i16

unfold
let mm256_storeu_si256_i16 = mm256_storeu_si256_i16'

assume
val mm256_storeu_si256_i32':
    output: t_Slice i32 ->
    vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> t_Slice i32

unfold
let mm256_storeu_si256_i32 = mm256_storeu_si256_i32'

assume
val mm_storeu_si128':
    output: t_Slice i16 ->
    vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> t_Slice i16

unfold
let mm_storeu_si128 = mm_storeu_si128'

assume
val mm_storeu_si128_i32':
    output: t_Slice i32 ->
    vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> t_Slice i32

unfold
let mm_storeu_si128_i32 = mm_storeu_si128_i32'

assume
val mm_storeu_bytes_si128':
    output: t_Slice u8 ->
    vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Prims.Pure (t_Slice u8)
      Prims.l_True
      (ensures
        fun output_future ->
          let output_future:t_Slice u8 = output_future in
          (Core.Slice.impl__len #u8 output_future <: usize) =.
          (Core.Slice.impl__len #u8 output <: usize))

unfold
let mm_storeu_bytes_si128 = mm_storeu_bytes_si128'

assume
val mm_loadu_si128': input: t_Slice u8 -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let mm_loadu_si128 = mm_loadu_si128'

assume
val mm256_loadu_si256_u8': input: t_Slice u8
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let mm256_loadu_si256_u8 = mm256_loadu_si256_u8'

assume
val mm256_loadu_si256_i16': input: t_Slice i16
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let mm256_loadu_si256_i16 = mm256_loadu_si256_i16'

assume
val mm256_loadu_si256_i32': input: t_Slice i32
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let mm256_loadu_si256_i32 = mm256_loadu_si256_i32'

let mm256_setzero_si256 (_: Prims.unit) : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx.e_mm256_setzero_si256 ()

let mm256_set_m128i (hi lo: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx.e_mm256_set_m128i hi lo

[@@ "opaque_to_smt"]

let mm_set_epi8
      (byte15 byte14 byte13 byte12 byte11 byte10 byte9 byte8 byte7 byte6 byte5 byte4 byte3 byte2 byte1 byte0:
          u8)
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Core_models.Core_arch.X86.Sse2.e_mm_set_epi8 (cast (byte15 <: u8) <: i8)
    (cast (byte14 <: u8) <: i8) (cast (byte13 <: u8) <: i8) (cast (byte12 <: u8) <: i8)
    (cast (byte11 <: u8) <: i8) (cast (byte10 <: u8) <: i8) (cast (byte9 <: u8) <: i8)
    (cast (byte8 <: u8) <: i8) (cast (byte7 <: u8) <: i8) (cast (byte6 <: u8) <: i8)
    (cast (byte5 <: u8) <: i8) (cast (byte4 <: u8) <: i8) (cast (byte3 <: u8) <: i8)
    (cast (byte2 <: u8) <: i8) (cast (byte1 <: u8) <: i8) (cast (byte0 <: u8) <: i8)

[@@ "opaque_to_smt"]

let mm256_set_epi8
      (byte31 byte30 byte29 byte28 byte27 byte26 byte25 byte24 byte23 byte22 byte21 byte20 byte19 byte18 byte17 byte16 byte15 byte14 byte13 byte12 byte11 byte10 byte9 byte8 byte7 byte6 byte5 byte4 byte3 byte2 byte1 byte0:
          i8)
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx.e_mm256_set_epi8 byte31 byte30 byte29 byte28 byte27 byte26 byte25
    byte24 byte23 byte22 byte21 byte20 byte19 byte18 byte17 byte16 byte15 byte14 byte13 byte12
    byte11 byte10 byte9 byte8 byte7 byte6 byte5 byte4 byte3 byte2 byte1 byte0

[@@ "opaque_to_smt"]

let mm256_set1_epi16 (constant: i16) : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx.e_mm256_set1_epi16 constant

[@@ "opaque_to_smt"]

let mm256_set_epi16
      (input15 input14 input13 input12 input11 input10 input9 input8 input7 input6 input5 input4 input3 input2 input1 input0:
          i16)
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx.e_mm256_set_epi16 input15 input14 input13 input12 input11 input10
    input9 input8 input7 input6 input5 input4 input3 input2 input1 input0

[@@ "opaque_to_smt"]

let mm_set1_epi16 (constant: i16) : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Core_models.Core_arch.X86.Sse2.e_mm_set1_epi16 constant

[@@ "opaque_to_smt"]

let mm256_set1_epi32 (constant: i32) : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx.e_mm256_set1_epi32 constant

[@@ "opaque_to_smt"]

let mm_set_epi32 (input3 input2 input1 input0: i32)
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Core_models.Core_arch.X86.Sse2.e_mm_set_epi32 input3 input2 input1 input0

[@@ "opaque_to_smt"]

let mm256_set_epi32 (input7 input6 input5 input4 input3 input2 input1 input0: i32)
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx.e_mm256_set_epi32 input7
    input6
    input5
    input4
    input3
    input2
    input1
    input0

[@@ "opaque_to_smt"]

let mm_add_epi16 (lhs rhs: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Core_models.Core_arch.X86.Sse2.e_mm_add_epi16 lhs rhs

[@@ "opaque_to_smt"]

let mm256_add_epi16 (lhs rhs: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_add_epi16 lhs rhs

[@@ "opaque_to_smt"]

let mm256_madd_epi16 (lhs rhs: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_madd_epi16 lhs rhs

[@@ "opaque_to_smt"]

let mm256_add_epi32 (lhs rhs: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_add_epi32 lhs rhs

[@@ "opaque_to_smt"]

let mm256_add_epi64 (lhs rhs: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_add_epi64 lhs rhs

[@@ "opaque_to_smt"]

let mm256_abs_epi32 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_abs_epi32 a

[@@ "opaque_to_smt"]

let mm256_sub_epi16 (lhs rhs: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_sub_epi16 lhs rhs

[@@ "opaque_to_smt"]

let mm256_sub_epi32 (lhs rhs: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_sub_epi32 lhs rhs

[@@ "opaque_to_smt"]

let mm_sub_epi16 (lhs rhs: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Core_models.Core_arch.X86.Sse2.e_mm_sub_epi16 lhs rhs

[@@ "opaque_to_smt"]

let mm256_mullo_epi16 (lhs rhs: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_mullo_epi16 lhs rhs

[@@ "opaque_to_smt"]

let mm_mullo_epi16 (lhs rhs: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Core_models.Core_arch.X86.Sse2.e_mm_mullo_epi16 lhs rhs

[@@ "opaque_to_smt"]

let mm256_cmpgt_epi16 (lhs rhs: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_cmpgt_epi16 lhs rhs

[@@ "opaque_to_smt"]

let mm256_cmpgt_epi32 (lhs rhs: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_cmpgt_epi32 lhs rhs

[@@ "opaque_to_smt"]

let mm256_cmpeq_epi32 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_cmpeq_epi32 a b

[@@ "opaque_to_smt"]

let mm256_sign_epi32 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_sign_epi32 a b

[@@ "opaque_to_smt"]

let mm256_castsi256_ps (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx.e_mm256_castsi256_ps a

[@@ "opaque_to_smt"]

let mm256_castps_si256 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx.e_mm256_castps_si256 a

[@@ "opaque_to_smt"]

let mm256_movemask_ps (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) : i32 =
  Core_models.Core_arch.X86.Avx.e_mm256_movemask_ps a

[@@ "opaque_to_smt"]

let mm_mulhi_epi16 (lhs rhs: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Core_models.Core_arch.X86.Sse2.e_mm_mulhi_epi16 lhs rhs

[@@ "opaque_to_smt"]

let mm256_mullo_epi32 (lhs rhs: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_mullo_epi32 lhs rhs

[@@ "opaque_to_smt"]

let mm256_mulhi_epi16 (lhs rhs: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_mulhi_epi16 lhs rhs

[@@ "opaque_to_smt"]

let mm256_mul_epu32 (lhs rhs: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_mul_epu32 lhs rhs

[@@ "opaque_to_smt"]

let mm256_mul_epi32 (lhs rhs: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_mul_epi32 lhs rhs

[@@ "opaque_to_smt"]

let mm256_and_si256 (lhs rhs: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_and_si256 lhs rhs

[@@ "opaque_to_smt"]

let mm256_or_si256 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_or_si256 a b

[@@ "opaque_to_smt"]

let mm256_testz_si256 (lhs rhs: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) : i32 =
  Core_models.Core_arch.X86.Avx.e_mm256_testz_si256 lhs rhs

[@@ "opaque_to_smt"]

let mm256_xor_si256 (lhs rhs: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_xor_si256 lhs rhs

[@@ "opaque_to_smt"]

let mm256_srai_epi16
      (v_SHIFT_BY: i32)
      (vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_srai_epi16 v_SHIFT_BY vector

[@@ "opaque_to_smt"]

let mm256_srai_epi32
      (v_SHIFT_BY: i32)
      (vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_srai_epi32 v_SHIFT_BY vector

[@@ "opaque_to_smt"]

let mm256_srli_epi16
      (v_SHIFT_BY: i32)
      (vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_srli_epi16 v_SHIFT_BY vector

[@@ "opaque_to_smt"]

let mm256_srli_epi32
      (v_SHIFT_BY: i32)
      (vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_srli_epi32 v_SHIFT_BY vector

[@@ "opaque_to_smt"]

let mm_srli_epi64 (v_SHIFT_BY: i32) (vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Core_models.Core_arch.X86.Sse2.e_mm_srli_epi64 v_SHIFT_BY vector

[@@ "opaque_to_smt"]

let mm256_srli_epi64
      (v_SHIFT_BY: i32)
      (vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Prims.Pure (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (requires v_SHIFT_BY >. mk_i32 0 && v_SHIFT_BY <. mk_i32 64)
      (fun _ -> Prims.l_True) = Core_models.Core_arch.X86.Avx2.e_mm256_srli_epi64 v_SHIFT_BY vector

[@@ "opaque_to_smt"]

let mm256_slli_epi16
      (v_SHIFT_BY: i32)
      (vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_slli_epi16 v_SHIFT_BY vector

[@@ "opaque_to_smt"]

let mm256_slli_epi32
      (v_SHIFT_BY: i32)
      (vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_slli_epi32 v_SHIFT_BY vector

[@@ "opaque_to_smt"]

let mm_shuffle_epi8 (vector control: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Core_models.Core_arch.X86.Ssse3.e_mm_shuffle_epi8 vector control

[@@ "opaque_to_smt"]

let mm256_shuffle_epi8 (vector control: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_shuffle_epi8 vector control

[@@ "opaque_to_smt"]

let mm256_shuffle_epi32
      (v_CONTROL: i32)
      (vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_shuffle_epi32 v_CONTROL vector

[@@ "opaque_to_smt"]

let mm256_permute4x64_epi64
      (v_CONTROL: i32)
      (vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_permute4x64_epi64 v_CONTROL vector

[@@ "opaque_to_smt"]

let mm256_unpackhi_epi64 (lhs rhs: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_unpackhi_epi64 lhs rhs

[@@ "opaque_to_smt"]

let mm256_unpacklo_epi32 (lhs rhs: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_unpacklo_epi32 lhs rhs

[@@ "opaque_to_smt"]

let mm256_unpackhi_epi32 (lhs rhs: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_unpackhi_epi32 lhs rhs

[@@ "opaque_to_smt"]

let mm256_castsi256_si128 (vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Core_models.Core_arch.X86.Avx.e_mm256_castsi256_si128 vector

[@@ "opaque_to_smt"]

let mm256_castsi128_si256 (vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx.e_mm256_castsi128_si256 vector

[@@ "opaque_to_smt"]

let mm256_cvtepi16_epi32 (vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_cvtepi16_epi32 vector

[@@ "opaque_to_smt"]

let mm_packs_epi16 (lhs rhs: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Core_models.Core_arch.X86.Sse2.e_mm_packs_epi16 lhs rhs

[@@ "opaque_to_smt"]

let mm256_packs_epi32 (lhs rhs: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_packs_epi32 lhs rhs

[@@ "opaque_to_smt"]

let mm256_extracti128_si256
      (v_CONTROL: i32)
      (vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Core_models.Core_arch.X86.Avx2.e_mm256_extracti128_si256 v_CONTROL vector

[@@ "opaque_to_smt"]

let mm256_inserti128_si256
      (v_CONTROL: i32)
      (vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (vector_i128: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_inserti128_si256 v_CONTROL vector vector_i128

[@@ "opaque_to_smt"]

let mm256_blend_epi16
      (v_CONTROL: i32)
      (lhs rhs: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_blend_epi16 v_CONTROL lhs rhs

[@@ "opaque_to_smt"]

let mm256_blend_epi32
      (v_CONTROL: i32)
      (lhs rhs: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_blend_epi32 v_CONTROL lhs rhs

[@@ "opaque_to_smt"]

let vec256_blendv_epi32 (a b mask: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx.e_mm256_castps_si256 (Core_models.Core_arch.X86.Avx.e_mm256_blendv_ps
        (Core_models.Core_arch.X86.Avx.e_mm256_castsi256_ps a
          <:
          Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        (Core_models.Core_arch.X86.Avx.e_mm256_castsi256_ps b
          <:
          Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        (Core_models.Core_arch.X86.Avx.e_mm256_castsi256_ps mask
          <:
          Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      <:
      Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))

[@@ "opaque_to_smt"]

let mm_movemask_epi8 (vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)) : i32 =
  Core_models.Core_arch.X86.Sse2.e_mm_movemask_epi8 vector

[@@ "opaque_to_smt"]

let mm256_permutevar8x32_epi32
      (vector control: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_permutevar8x32_epi32 vector control

[@@ "opaque_to_smt"]

let mm256_srlv_epi32 (vector counts: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_srlv_epi32 vector counts

[@@ "opaque_to_smt"]

let mm256_srlv_epi64 (vector counts: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_srlv_epi64 vector counts

[@@ "opaque_to_smt"]

let mm_sllv_epi32 (vector counts: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Core_models.Core_arch.X86.Avx2.e_mm_sllv_epi32 vector counts

[@@ "opaque_to_smt"]

let mm256_sllv_epi32 (vector counts: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_sllv_epi32 vector counts

[@@ "opaque_to_smt"]

let mm256_slli_epi64 (v_LEFT: i32) (x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_slli_epi64 v_LEFT x

[@@ "opaque_to_smt"]

let mm256_bsrli_epi128 (v_SHIFT_BY: i32) (x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_bsrli_epi128 v_SHIFT_BY x

[@@ "opaque_to_smt"]

let mm256_andnot_si256 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_andnot_si256 a b

[@@ "opaque_to_smt"]

let mm256_set1_epi64x (a: i64) : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx.e_mm256_set1_epi64x a

[@@ "opaque_to_smt"]

let mm256_set_epi64x (input3 input2 input1 input0: i64)
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx.e_mm256_set_epi64x input3 input2 input1 input0

[@@ "opaque_to_smt"]

let mm256_unpacklo_epi64 (lhs rhs: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_unpacklo_epi64 lhs rhs

[@@ "opaque_to_smt"]

let mm256_permute2x128_si256
      (v_IMM8: i32)
      (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Core_arch.X86.Avx2.e_mm256_permute2x128_si256 v_IMM8 a b
