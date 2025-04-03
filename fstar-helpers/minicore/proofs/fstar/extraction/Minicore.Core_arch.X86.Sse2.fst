module Minicore.Core_arch.X86.Sse2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

assume
val e_mm_set_epi8':
    e15: i8 ->
    e14: i8 ->
    e13: i8 ->
    e12: i8 ->
    e11: i8 ->
    e10: i8 ->
    e9: i8 ->
    e8: i8 ->
    e7: i8 ->
    e6: i8 ->
    e5: i8 ->
    e4: i8 ->
    e3: i8 ->
    e2: i8 ->
    e1: i8 ->
    e0: i8
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)

let e_mm_set_epi8 = e_mm_set_epi8'
