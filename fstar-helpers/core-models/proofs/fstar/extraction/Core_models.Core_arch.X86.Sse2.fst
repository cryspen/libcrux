module Core_models.Core_arch.X86.Sse2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

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
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_mm_set_epi8 = e_mm_set_epi8'
