module Libcrux_core_models.Core_arch.X86.Sse2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_packs_epi16)
assume
val e_mm_packs_epi16':
    Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_mm_packs_epi16 = e_mm_packs_epi16'

assume
val e_mm_set_epi8':
    e_e15: i8 ->
    e_e14: i8 ->
    e_e13: i8 ->
    e_e12: i8 ->
    e_e11: i8 ->
    e_e10: i8 ->
    e_e9: i8 ->
    e_e8: i8 ->
    e_e7: i8 ->
    e_e6: i8 ->
    e_e5: i8 ->
    e_e4: i8 ->
    e_e3: i8 ->
    e_e2: i8 ->
    e_e1: i8 ->
    e_e0: i8
  -> Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_mm_set_epi8 = e_mm_set_epi8'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_set1_epi16)
assume
val e_mm_set1_epi16': i16 -> Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_mm_set1_epi16 = e_mm_set1_epi16'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_set_epi32)
assume
val e_mm_set_epi32': i32 -> i32 -> i32 -> i32
  -> Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_mm_set_epi32 = e_mm_set_epi32'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_add_epi16)
assume
val e_mm_add_epi16':
    Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_mm_add_epi16 = e_mm_add_epi16'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sub_epi16)
assume
val e_mm_sub_epi16':
    Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_mm_sub_epi16 = e_mm_sub_epi16'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_mullo_epi16)
assume
val e_mm_mullo_epi16':
    Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_mm_mullo_epi16 = e_mm_mullo_epi16'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_mulhi_epi16)
assume
val e_mm_mulhi_epi16':
    Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_mm_mulhi_epi16 = e_mm_mulhi_epi16'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_srli_epi64)
assume
val e_mm_srli_epi64': v_IMM8: i32 -> Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_mm_srli_epi64 (v_IMM8: i32) = e_mm_srli_epi64' v_IMM8

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_movemask_epi8)
assume
val e_mm_movemask_epi8': Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) -> i32

unfold
let e_mm_movemask_epi8 = e_mm_movemask_epi8'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_unpacklo_epi64)
assume
val e_mm_unpacklo_epi64':
    Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_mm_unpacklo_epi64 = e_mm_unpacklo_epi64'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_unpackhi_epi64)
assume
val e_mm_unpackhi_epi64':
    Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_mm_unpackhi_epi64 = e_mm_unpackhi_epi64'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_shuffle_epi32)
assume
val e_mm_shuffle_epi32': v_IMM8: i32 -> Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_mm_shuffle_epi32 (v_IMM8: i32) = e_mm_shuffle_epi32' v_IMM8

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_srli_si128)
assume
val e_mm_srli_si128': v_IMM8: i32 -> Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_mm_srli_si128 (v_IMM8: i32) = e_mm_srli_si128' v_IMM8

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_slli_si128)
assume
val e_mm_slli_si128': v_IMM8: i32 -> Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_mm_slli_si128 (v_IMM8: i32) = e_mm_slli_si128' v_IMM8

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_xor_si128)
assume
val e_mm_xor_si128':
    Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_mm_xor_si128 = e_mm_xor_si128'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_setzero_si128)
assume
val e_mm_setzero_si128': Prims.unit -> Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_mm_setzero_si128 = e_mm_setzero_si128'
