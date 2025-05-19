module Core_models.Core_arch.X86.Opaque
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

assume
val e_mm256_setzero_si256': Prims.unit -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_setzero_si256 = e_mm256_setzero_si256'

assume
val e_mm256_set_m128i':
    hi: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    lo: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_set_m128i = e_mm256_set_m128i'

assume
val e_mm256_set1_epi16': a: i16 -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_set1_epi16 = e_mm256_set1_epi16'

assume
val e_mm_set1_epi16': a: i16 -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_mm_set1_epi16 = e_mm_set1_epi16'

assume
val e_mm_set_epi32': e3: i32 -> e2: i32 -> e1: i32 -> e0: i32
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_mm_set_epi32 = e_mm_set_epi32'

assume
val e_mm_add_epi16':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_mm_add_epi16 = e_mm_add_epi16'

assume
val e_mm256_add_epi16':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_add_epi16 = e_mm256_add_epi16'

assume
val e_mm256_madd_epi16':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_madd_epi16 = e_mm256_madd_epi16'

assume
val e_mm256_add_epi32':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_add_epi32 = e_mm256_add_epi32'

assume
val e_mm256_add_epi64':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_add_epi64 = e_mm256_add_epi64'

assume
val e_mm256_abs_epi32': a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_abs_epi32 = e_mm256_abs_epi32'

assume
val e_mm256_sub_epi16':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_sub_epi16 = e_mm256_sub_epi16'

assume
val e_mm_sub_epi16':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_mm_sub_epi16 = e_mm_sub_epi16'

assume
val e_mm_mullo_epi16':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_mm_mullo_epi16 = e_mm_mullo_epi16'

assume
val e_mm256_cmpgt_epi16':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_cmpgt_epi16 = e_mm256_cmpgt_epi16'

assume
val e_mm256_cmpgt_epi32':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_cmpgt_epi32 = e_mm256_cmpgt_epi32'

assume
val e_mm256_cmpeq_epi32':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_cmpeq_epi32 = e_mm256_cmpeq_epi32'

assume
val e_mm256_sign_epi32':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_sign_epi32 = e_mm256_sign_epi32'

assume
val e_mm256_castsi256_ps': a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Core_arch.X86.t_e_ee_m256

unfold
let e_mm256_castsi256_ps = e_mm256_castsi256_ps'

assume
val e_mm256_castps_si256': a: Core_models.Core_arch.X86.t_e_ee_m256
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_castps_si256 = e_mm256_castps_si256'

assume
val e_mm256_movemask_ps': a: Core_models.Core_arch.X86.t_e_ee_m256 -> i32

unfold
let e_mm256_movemask_ps = e_mm256_movemask_ps'

assume
val e_mm_mulhi_epi16':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_mm_mulhi_epi16 = e_mm_mulhi_epi16'

assume
val e_mm256_mullo_epi32':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_mullo_epi32 = e_mm256_mullo_epi32'

assume
val e_mm256_mulhi_epi16':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_mulhi_epi16 = e_mm256_mulhi_epi16'

assume
val e_mm256_mul_epu32':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_mul_epu32 = e_mm256_mul_epu32'

assume
val e_mm256_and_si256':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_and_si256 = e_mm256_and_si256'

assume
val e_mm256_or_si256':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_or_si256 = e_mm256_or_si256'

assume
val e_mm256_testz_si256':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> i32

unfold
let e_mm256_testz_si256 = e_mm256_testz_si256'

assume
val e_mm256_xor_si256':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_xor_si256 = e_mm256_xor_si256'

assume
val e_mm256_srai_epi16': v_IMM8: i32 -> a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_srai_epi16 (v_IMM8: i32) = e_mm256_srai_epi16' v_IMM8

assume
val e_mm256_srai_epi32': v_IMM8: i32 -> a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_srai_epi32 (v_IMM8: i32) = e_mm256_srai_epi32' v_IMM8

assume
val e_mm256_srli_epi16': v_IMM8: i32 -> a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_srli_epi16 (v_IMM8: i32) = e_mm256_srli_epi16' v_IMM8

assume
val e_mm256_srli_epi32': v_IMM8: i32 -> a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_srli_epi32 (v_IMM8: i32) = e_mm256_srli_epi32' v_IMM8

assume
val e_mm_srli_epi64': v_IMM8: i32 -> a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_mm_srli_epi64 (v_IMM8: i32) = e_mm_srli_epi64' v_IMM8

assume
val e_mm256_slli_epi32': v_IMM8: i32 -> a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_slli_epi32 (v_IMM8: i32) = e_mm256_slli_epi32' v_IMM8

assume
val e_mm256_permute4x64_epi64':
    v_IMM8: i32 ->
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_permute4x64_epi64 (v_IMM8: i32) = e_mm256_permute4x64_epi64' v_IMM8

assume
val e_mm256_unpackhi_epi64':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_unpackhi_epi64 = e_mm256_unpackhi_epi64'

assume
val e_mm256_unpacklo_epi32':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_unpacklo_epi32 = e_mm256_unpacklo_epi32'

assume
val e_mm256_unpackhi_epi32':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_unpackhi_epi32 = e_mm256_unpackhi_epi32'

assume
val e_mm256_castsi128_si256': a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_castsi128_si256 = e_mm256_castsi128_si256'

assume
val e_mm256_cvtepi16_epi32': a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_cvtepi16_epi32 = e_mm256_cvtepi16_epi32'

assume
val e_mm_packs_epi16':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_mm_packs_epi16 = e_mm_packs_epi16'

assume
val e_mm256_packs_epi32':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_packs_epi32 = e_mm256_packs_epi32'

assume
val e_mm256_inserti128_si256':
    v_IMM8: i32 ->
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_inserti128_si256 (v_IMM8: i32) = e_mm256_inserti128_si256' v_IMM8

assume
val e_mm256_blend_epi16':
    v_IMM8: i32 ->
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_blend_epi16 (v_IMM8: i32) = e_mm256_blend_epi16' v_IMM8

assume
val e_mm256_blendv_ps':
    a: Core_models.Core_arch.X86.t_e_ee_m256 ->
    b: Core_models.Core_arch.X86.t_e_ee_m256 ->
    mask: Core_models.Core_arch.X86.t_e_ee_m256
  -> Core_models.Core_arch.X86.t_e_ee_m256

unfold
let e_mm256_blendv_ps = e_mm256_blendv_ps'

assume
val e_mm_movemask_epi8': a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) -> i32

unfold
let e_mm_movemask_epi8 = e_mm_movemask_epi8'

assume
val e_mm256_srlv_epi64':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_srlv_epi64 = e_mm256_srlv_epi64'

assume
val e_mm_sllv_epi32':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_mm_sllv_epi32 = e_mm_sllv_epi32'

assume
val e_mm256_slli_epi64': v_IMM8: i32 -> a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_slli_epi64 (v_IMM8: i32) = e_mm256_slli_epi64' v_IMM8

assume
val e_mm256_bsrli_epi128': v_IMM8: i32 -> a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_bsrli_epi128 (v_IMM8: i32) = e_mm256_bsrli_epi128' v_IMM8

assume
val e_mm256_andnot_si256':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_andnot_si256 = e_mm256_andnot_si256'

assume
val e_mm256_set1_epi64x': a: i64 -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_set1_epi64x = e_mm256_set1_epi64x'

assume
val e_mm256_set_epi64x': e3: i64 -> e2: i64 -> e1: i64 -> e0: i64
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_set_epi64x = e_mm256_set_epi64x'

assume
val e_mm256_unpacklo_epi64':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_unpacklo_epi64 = e_mm256_unpacklo_epi64'

assume
val e_mm256_permute2x128_si256':
    v_IMM8: i32 ->
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_permute2x128_si256 (v_IMM8: i32) = e_mm256_permute2x128_si256' v_IMM8
