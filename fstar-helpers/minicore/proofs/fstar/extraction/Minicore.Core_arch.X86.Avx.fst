module Minicore.Core_arch.X86.Avx
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Minicore.Abstractions.Bitvec in
  ()

let e_mm256_castsi256_si128 (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Minicore.Abstractions.Bitvec.impl_9__from_fn (mk_u64 128)
    (fun i ->
        let i:u64 = i in
        vector.[ i ] <: Minicore.Abstractions.Bit.t_Bit)

assume
val e_mm256_set1_epi32': i32 -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let e_mm256_set1_epi32 = e_mm256_set1_epi32'

assume
val e_mm256_set_epi32':
    e_e0: i32 ->
    e_e1: i32 ->
    e_e2: i32 ->
    e_e3: i32 ->
    e_e4: i32 ->
    e_e5: i32 ->
    e_e6: i32 ->
    e_e7: i32
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let e_mm256_set_epi32 = e_mm256_set_epi32'

assume
val e_mm256_set_epi16':
    e_e00: i16 ->
    e_e01: i16 ->
    e_e02: i16 ->
    e_e03: i16 ->
    e_e04: i16 ->
    e_e05: i16 ->
    e_e06: i16 ->
    e_e07: i16 ->
    e_e08: i16 ->
    e_e09: i16 ->
    e_e10: i16 ->
    e_e11: i16 ->
    e_e12: i16 ->
    e_e13: i16 ->
    e_e14: i16 ->
    e_e15: i16
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let e_mm256_set_epi16 = e_mm256_set_epi16'

assume
val e_mm256_set_epi8':
    e_e00: i8 ->
    e_e01: i8 ->
    e_e02: i8 ->
    e_e03: i8 ->
    e_e04: i8 ->
    e_e05: i8 ->
    e_e06: i8 ->
    e_e07: i8 ->
    e_e08: i8 ->
    e_e09: i8 ->
    e_e10: i8 ->
    e_e11: i8 ->
    e_e12: i8 ->
    e_e13: i8 ->
    e_e14: i8 ->
    e_e15: i8 ->
    e_e16: i8 ->
    e_e17: i8 ->
    e_e18: i8 ->
    e_e19: i8 ->
    e_e20: i8 ->
    e_e21: i8 ->
    e_e22: i8 ->
    e_e23: i8 ->
    e_e24: i8 ->
    e_e25: i8 ->
    e_e26: i8 ->
    e_e27: i8 ->
    e_e28: i8 ->
    e_e29: i8 ->
    e_e30: i8 ->
    e_e31: i8
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let e_mm256_set_epi8 = e_mm256_set_epi8'
