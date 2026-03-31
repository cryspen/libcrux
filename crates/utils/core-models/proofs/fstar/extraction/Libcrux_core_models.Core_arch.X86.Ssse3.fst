module Libcrux_core_models.Core_arch.X86.Ssse3
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

assume
val e_mm_shuffle_epi8':
    vector: Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    indexes: Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_mm_shuffle_epi8 = e_mm_shuffle_epi8'
