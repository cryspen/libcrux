module Libcrux_core_models.Core_arch.X86.Other
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_aeskeygenassist_si128)
assume
val e_mm_aeskeygenassist_si128': Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) -> i32
  -> Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_mm_aeskeygenassist_si128 = e_mm_aeskeygenassist_si128'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_aesenclast_si128)
assume
val e_mm_aesenclast_si128':
    Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_mm_aesenclast_si128 = e_mm_aesenclast_si128'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_aesenc_si128)
assume
val e_mm_aesenc_si128':
    Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_mm_aesenc_si128 = e_mm_aesenc_si128'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_clmulepi64_si128)
assume
val e_mm_clmulepi64_si128':
    Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    i32
  -> Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_mm_clmulepi64_si128 = e_mm_clmulepi64_si128'
