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
val e_mm256_set_epi32':
    e0: i32 ->
    e1: i32 ->
    e2: i32 ->
    e3: i32 ->
    e4: i32 ->
    e5: i32 ->
    e6: i32 ->
    e7: i32
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let e_mm256_set_epi32 = e_mm256_set_epi32'

assume
val e_mm256_set_epi16':
    e00: i16 ->
    e01: i16 ->
    e02: i16 ->
    e03: i16 ->
    e04: i16 ->
    e05: i16 ->
    e06: i16 ->
    e07: i16 ->
    e08: i16 ->
    e09: i16 ->
    e10: i16 ->
    e11: i16 ->
    e12: i16 ->
    e13: i16 ->
    e14: i16 ->
    e15: i16
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let e_mm256_set_epi16 = e_mm256_set_epi16'

assume
val e_mm256_set_epi8':
    e00: i8 ->
    e01: i8 ->
    e02: i8 ->
    e03: i8 ->
    e04: i8 ->
    e05: i8 ->
    e06: i8 ->
    e07: i8 ->
    e08: i8 ->
    e09: i8 ->
    e10: i8 ->
    e11: i8 ->
    e12: i8 ->
    e13: i8 ->
    e14: i8 ->
    e15: i8 ->
    e16: i8 ->
    e17: i8 ->
    e18: i8 ->
    e19: i8 ->
    e20: i8 ->
    e21: i8 ->
    e22: i8 ->
    e23: i8 ->
    e24: i8 ->
    e25: i8 ->
    e26: i8 ->
    e27: i8 ->
    e28: i8 ->
    e29: i8 ->
    e30: i8 ->
    e31: i8
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let e_mm256_set_epi8 = e_mm256_set_epi8'
