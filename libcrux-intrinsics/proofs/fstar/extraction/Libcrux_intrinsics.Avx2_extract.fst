module Libcrux_intrinsics.Avx2_extract
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

assume
val mm256_storeu_si256_u8':
    output: t_Slice u8 ->
    vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> t_Slice u8

let mm256_storeu_si256_u8 = mm256_storeu_si256_u8'

assume
val mm256_storeu_si256_i16':
    output: t_Slice i16 ->
    vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Prims.Pure (t_Slice i16)
      Prims.l_True
      (ensures
        fun output_future ->
          let output_future:t_Slice i16 = output_future in
          (Core.Slice.impl__len #i16 output_future <: usize) =.
          (Core.Slice.impl__len #i16 output <: usize))

let mm256_storeu_si256_i16 = mm256_storeu_si256_i16'

assume
val mm256_storeu_si256_i32':
    output: t_Slice i32 ->
    vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> t_Slice i32

let mm256_storeu_si256_i32 = mm256_storeu_si256_i32'

assume
val mm_storeu_si128':
    output: t_Slice i16 ->
    vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> t_Slice i16

let mm_storeu_si128 = mm_storeu_si128'

assume
val mm_storeu_si128_i32':
    output: t_Slice i32 ->
    vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> t_Slice i32

let mm_storeu_si128_i32 = mm_storeu_si128_i32'

assume
val mm_storeu_bytes_si128':
    output: t_Slice u8 ->
    vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Prims.Pure (t_Slice u8)
      Prims.l_True
      (ensures
        fun output_future ->
          let output_future:t_Slice u8 = output_future in
          (Core.Slice.impl__len #u8 output <: usize) =.
          (Core.Slice.impl__len #u8 output_future <: usize))

let mm_storeu_bytes_si128 = mm_storeu_bytes_si128'

assume
val mm_loadu_si128': input: t_Slice u8 -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)

let mm_loadu_si128 = mm_loadu_si128'

assume
val mm256_loadu_si256_u8': input: t_Slice u8 -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_loadu_si256_u8 = mm256_loadu_si256_u8'

assume
val mm256_loadu_si256_i16': input: t_Slice i16 -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_loadu_si256_i16 = mm256_loadu_si256_i16'

assume
val mm256_loadu_si256_i32': input: t_Slice i32 -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_loadu_si256_i32 = mm256_loadu_si256_i32'

assume
val mm256_setzero_si256': Prims.unit -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_setzero_si256 = mm256_setzero_si256'

assume
val mm256_set_m128i':
    hi: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    lo: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_set_m128i = mm256_set_m128i'

let mm_set_epi8
      (byte15 byte14 byte13 byte12 byte11 byte10 byte9 byte8 byte7 byte6 byte5 byte4 byte3 byte2 byte1 byte0:
          u8)
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Minicore.Arch.X86.e_mm_set_epi8 (cast (byte15 <: u8) <: i8) (cast (byte14 <: u8) <: i8)
    (cast (byte13 <: u8) <: i8) (cast (byte12 <: u8) <: i8) (cast (byte11 <: u8) <: i8)
    (cast (byte10 <: u8) <: i8) (cast (byte9 <: u8) <: i8) (cast (byte8 <: u8) <: i8)
    (cast (byte7 <: u8) <: i8) (cast (byte6 <: u8) <: i8) (cast (byte5 <: u8) <: i8)
    (cast (byte4 <: u8) <: i8) (cast (byte3 <: u8) <: i8) (cast (byte2 <: u8) <: i8)
    (cast (byte1 <: u8) <: i8) (cast (byte0 <: u8) <: i8)

assume
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
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_set_epi8 = mm256_set_epi8'

assume
val mm256_set1_epi16': constant: i16 -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_set1_epi16 = mm256_set1_epi16'

assume
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
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_set_epi16 = mm256_set_epi16'

assume
val mm_set1_epi16': constant: i16 -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)

let mm_set1_epi16 = mm_set1_epi16'

assume
val mm256_set1_epi32': constant: i32 -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_set1_epi32 = mm256_set1_epi32'

assume
val mm_set_epi32': input3: i32 -> input2: i32 -> input1: i32 -> input0: i32
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)

let mm_set_epi32 = mm_set_epi32'

let mm256_set_epi32 (x7 x6 x5 x4 x3 x2 x1 x0: i32)
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Minicore.Arch.X86.e_mm256_set_epi32 x7 x6 x5 x4 x3 x2 x1 x0

assume
val mm_add_epi16':
    lhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)

let mm_add_epi16 = mm_add_epi16'

assume
val mm_sub_epi16':
    lhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)

let mm_sub_epi16 = mm_sub_epi16'

assume
val mm256_add_epi16':
    lhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_add_epi16 = mm256_add_epi16'

assume
val mm256_madd_epi16':
    lhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_madd_epi16 = mm256_madd_epi16'

assume
val mm256_add_epi32':
    lhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_add_epi32 = mm256_add_epi32'

let mm256_sub_epi16 (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

assume
val mm256_add_epi64':
    lhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_add_epi64 = mm256_add_epi64'

assume
val mm256_abs_epi32': a: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_abs_epi32 = mm256_abs_epi32'

assume
val mm256_sub_epi32':
    lhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_sub_epi32 = mm256_sub_epi32'

assume
val mm256_mullo_epi16':
    lhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_mullo_epi16 = mm256_mullo_epi16'

assume
val mm_mullo_epi16':
    lhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)

let mm_mullo_epi16 = mm_mullo_epi16'

assume
val mm256_cmpgt_epi16':
    lhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_cmpgt_epi16 = mm256_cmpgt_epi16'

assume
val mm256_cmpgt_epi32':
    lhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_cmpgt_epi32 = mm256_cmpgt_epi32'

assume
val mm256_cmpeq_epi32':
    a: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_cmpeq_epi32 = mm256_cmpeq_epi32'

assume
val mm256_sign_epi32':
    a: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_sign_epi32 = mm256_sign_epi32'

assume
val mm256_castsi256_ps': a: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) -> u8

let mm256_castsi256_ps = mm256_castsi256_ps'

assume
val mm256_movemask_ps': a: u8 -> i32

let mm256_movemask_ps = mm256_movemask_ps'

assume
val mm_mulhi_epi16':
    lhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)

let mm_mulhi_epi16 = mm_mulhi_epi16'

assume
val mm256_mullo_epi32':
    lhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_mullo_epi32 = mm256_mullo_epi32'

assume
val mm256_mulhi_epi16':
    lhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_mulhi_epi16 = mm256_mulhi_epi16'

assume
val mm256_mul_epu32':
    lhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_mul_epu32 = mm256_mul_epu32'

assume
val mm256_mul_epi32':
    lhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_mul_epi32 = mm256_mul_epi32'

assume
val mm256_and_si256':
    lhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_and_si256 = mm256_and_si256'

assume
val mm256_or_si256':
    a: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_or_si256 = mm256_or_si256'

assume
val mm256_testz_si256':
    lhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> i32

let mm256_testz_si256 = mm256_testz_si256'

assume
val mm256_xor_si256':
    lhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_xor_si256 = mm256_xor_si256'

assume
val mm256_srai_epi16': v_SHIFT_BY: i32 -> vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Prims.Pure (Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (requires v_SHIFT_BY >=. mk_i32 0 && v_SHIFT_BY <. mk_i32 16)
      (fun _ -> Prims.l_True)

let mm256_srai_epi16 (v_SHIFT_BY: i32) = mm256_srai_epi16' v_SHIFT_BY

assume
val mm256_srai_epi32': v_SHIFT_BY: i32 -> vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_srai_epi32 (v_SHIFT_BY: i32) = mm256_srai_epi32' v_SHIFT_BY

assume
val mm256_srli_epi16': v_SHIFT_BY: i32 -> vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_srli_epi16 (v_SHIFT_BY: i32) = mm256_srli_epi16' v_SHIFT_BY

assume
val mm256_srli_epi32': v_SHIFT_BY: i32 -> vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_srli_epi32 (v_SHIFT_BY: i32) = mm256_srli_epi32' v_SHIFT_BY

assume
val mm_srli_epi64': v_SHIFT_BY: i32 -> vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)

let mm_srli_epi64 (v_SHIFT_BY: i32) = mm_srli_epi64' v_SHIFT_BY

let mm256_srli_epi64 (v_SHIFT_BY: i32) (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Minicore.Arch.X86.e_mm256_srli_epi64 v_SHIFT_BY vector

let mm256_slli_epi16 (v_SHIFT_BY: i32) (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Minicore.Arch.X86.e_mm256_slli_epi16 v_SHIFT_BY vector

assume
val mm256_slli_epi32': v_SHIFT_BY: i32 -> vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_slli_epi32 (v_SHIFT_BY: i32) = mm256_slli_epi32' v_SHIFT_BY

let mm_shuffle_epi8 (vector control: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Minicore.Arch.X86.e_mm_shuffle_epi8 vector control

assume
val mm256_shuffle_epi8':
    vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    control: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_shuffle_epi8 = mm256_shuffle_epi8'

assume
val mm256_shuffle_epi32':
    v_CONTROL: i32 ->
    vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_shuffle_epi32 (v_CONTROL: i32) = mm256_shuffle_epi32' v_CONTROL

assume
val mm256_permute4x64_epi64':
    v_CONTROL: i32 ->
    vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_permute4x64_epi64 (v_CONTROL: i32) = mm256_permute4x64_epi64' v_CONTROL

assume
val mm256_unpackhi_epi64':
    lhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_unpackhi_epi64 = mm256_unpackhi_epi64'

assume
val mm256_unpacklo_epi32':
    lhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_unpacklo_epi32 = mm256_unpacklo_epi32'

assume
val mm256_unpackhi_epi32':
    lhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_unpackhi_epi32 = mm256_unpackhi_epi32'

let mm256_castsi256_si128 (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Minicore.Arch.X86.e_mm256_castsi256_si128 vector

assume
val mm256_castsi128_si256': vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_castsi128_si256 = mm256_castsi128_si256'

assume
val mm256_cvtepi16_epi32': vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_cvtepi16_epi32 = mm256_cvtepi16_epi32'

assume
val mm_packs_epi16':
    lhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)

let mm_packs_epi16 = mm_packs_epi16'

assume
val mm256_packs_epi32':
    lhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_packs_epi32 = mm256_packs_epi32'

assume
val mm256_extracti128_si256':
    v_CONTROL: i32 ->
    vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)

let mm256_extracti128_si256 (v_CONTROL: i32) = mm256_extracti128_si256' v_CONTROL

assume
val mm256_inserti128_si256':
    v_CONTROL: i32 ->
    vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    vector_i128: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_inserti128_si256 (v_CONTROL: i32) = mm256_inserti128_si256' v_CONTROL

assume
val mm256_blend_epi16':
    v_CONTROL: i32 ->
    lhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_blend_epi16 (v_CONTROL: i32) = mm256_blend_epi16' v_CONTROL

assume
val mm256_blend_epi32':
    v_CONTROL: i32 ->
    lhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_blend_epi32 (v_CONTROL: i32) = mm256_blend_epi32' v_CONTROL

assume
val vec256_blendv_epi32':
    a: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    mask: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let vec256_blendv_epi32 = vec256_blendv_epi32'

assume
val mm_movemask_epi8': vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) -> i32

let mm_movemask_epi8 = mm_movemask_epi8'

let mm256_permutevar8x32_epi32 (vector control: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Minicore.Arch.X86.e_mm256_permutevar8x32_epi32 vector control

assume
val mm256_srlv_epi32':
    vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    counts: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_srlv_epi32 = mm256_srlv_epi32'

assume
val mm256_srlv_epi64':
    vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    counts: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_srlv_epi64 = mm256_srlv_epi64'

assume
val mm_sllv_epi32':
    vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    counts: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)

let mm_sllv_epi32 = mm_sllv_epi32'

let mm256_sllv_epi32 (vector counts: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Minicore.Arch.X86.e_mm256_sllv_epi32 vector counts

assume
val mm256_slli_epi64': v_LEFT: i32 -> x: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_slli_epi64 (v_LEFT: i32) = mm256_slli_epi64' v_LEFT

assume
val mm256_bsrli_epi128': v_SHIFT_BY: i32 -> x: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_bsrli_epi128 (v_SHIFT_BY: i32) = mm256_bsrli_epi128' v_SHIFT_BY

assume
val mm256_andnot_si256':
    a: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_andnot_si256 = mm256_andnot_si256'

assume
val mm256_set1_epi64x': a: i64 -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_set1_epi64x = mm256_set1_epi64x'

assume
val mm256_set_epi64x': input3: i64 -> input2: i64 -> input1: i64 -> input0: i64
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_set_epi64x = mm256_set_epi64x'

assume
val mm256_unpacklo_epi64':
    a: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_unpacklo_epi64 = mm256_unpacklo_epi64'

assume
val mm256_permute2x128_si256':
    v_IMM8: i32 ->
    a: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let mm256_permute2x128_si256 (v_IMM8: i32) = mm256_permute2x128_si256' v_IMM8
