module Minicore.Arch.X86
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Minicore.Abstractions.Bitvec in
  ()

let e_mm256_slli_epi16
      (v_SHIFT_BY: i32)
      (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Prims.Pure (Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (requires v_SHIFT_BY >=. mk_i32 0 && v_SHIFT_BY <. mk_i32 16)
      (fun _ -> Prims.l_True) =
  Minicore.Abstractions.Bitvec.impl_9__from_fn (mk_u64 256)
    (fun i ->
        let i:u64 = i in
        let nth_bit:u64 = i %! mk_u64 16 in
        let shift:u64 = cast (v_SHIFT_BY <: i32) <: u64 in
        if nth_bit >=. shift
        then vector.[ i -! shift <: u64 ]
        else Minicore.Abstractions.Bit.Bit_Zero <: Minicore.Abstractions.Bit.t_Bit)

let e_mm256_srli_epi64
      (v_SHIFT_BY: i32)
      (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Prims.Pure (Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (requires v_SHIFT_BY >=. mk_i32 0 && v_SHIFT_BY <. mk_i32 64)
      (fun _ -> Prims.l_True) =
  Minicore.Abstractions.Bitvec.impl_9__from_fn (mk_u64 256)
    (fun i ->
        let i:u64 = i in
        let nth_bit:u64 = i %! mk_u64 64 in
        let shift:u64 = cast (v_SHIFT_BY <: i32) <: u64 in
        if nth_bit <. (mk_u64 64 -! shift <: u64)
        then vector.[ i +! shift <: u64 ]
        else Minicore.Abstractions.Bit.Bit_Zero <: Minicore.Abstractions.Bit.t_Bit)

let e_mm256_castsi256_si128 (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Minicore.Abstractions.Bitvec.impl_9__from_fn (mk_u64 128)
    (fun i ->
        let i:u64 = i in
        vector.[ i ] <: Minicore.Abstractions.Bit.t_Bit)
