module Minicore.Core_arch.X86.Ssse3
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

assume
val e_mm_shuffle_epi8':
    vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    indexes: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)

let e_mm_shuffle_epi8 = e_mm_shuffle_epi8'
