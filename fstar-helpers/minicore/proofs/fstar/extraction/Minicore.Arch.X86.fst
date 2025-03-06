module Minicore.Arch.X86
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Minicore.Abstractions.Bitvec in
  ()

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

assume
val e_mm256_sllv_epi32':
    vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    counts: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let e_mm256_sllv_epi32 = e_mm256_sllv_epi32'

assume
val e_mm256_permutevar8x32_epi32':
    a: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let e_mm256_permutevar8x32_epi32 = e_mm256_permutevar8x32_epi32'

let e_mm256_castsi256_si128 (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Minicore.Abstractions.Bitvec.impl_9__from_fn (mk_u64 128)
    (fun i ->
        let i:u64 = i in
        vector.[ i ] <: Minicore.Abstractions.Bit.t_Bit)

assume
val e_mm_shuffle_epi8':
    vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    indexes: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)

let e_mm_shuffle_epi8 = e_mm_shuffle_epi8'

/// Rewrite lemmas
let e_: Prims.unit = ()

[@@ Minicore.Abstractions.Bitvec.v_REWRITE_RULE ]

assume
val e___e_rw_mm256_sllv_epi32':
    vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b7: i32 ->
    b6: i32 ->
    b5: i32 ->
    b4: i32 ->
    b3: i32 ->
    b2: i32 ->
    b1: i32 ->
    b0: i32
  -> Lemma
    (ensures
      (e_mm256_sllv_epi32 vector
          (e_mm256_set_epi32 b7 b6 b5 b4 b3 b2 b1 b0
            <:
            Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        <:
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Minicore.Arch.X86.Extra.mm256_sllv_epi32_u32 vector
          (cast (b7 <: i32) <: u32)
          (cast (b6 <: i32) <: u32)
          (cast (b5 <: i32) <: u32)
          (cast (b4 <: i32) <: u32)
          (cast (b3 <: i32) <: u32)
          (cast (b2 <: i32) <: u32)
          (cast (b1 <: i32) <: u32)
          (cast (b0 <: i32) <: u32)
        <:
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

let e___e_rw_mm256_sllv_epi32 = e___e_rw_mm256_sllv_epi32'

[@@ Minicore.Abstractions.Bitvec.v_REWRITE_RULE ]

assume
val e___e_rw_mm256_permutevar8x32_epi32':
    vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b7: i32 ->
    b6: i32 ->
    b5: i32 ->
    b4: i32 ->
    b3: i32 ->
    b2: i32 ->
    b1: i32 ->
    b0: i32
  -> Lemma
    (ensures
      (e_mm256_permutevar8x32_epi32 vector
          (e_mm256_set_epi32 b7 b6 b5 b4 b3 b2 b1 b0
            <:
            Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        <:
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Minicore.Arch.X86.Extra.mm256_permutevar8x32_epi32_u32 vector
          (cast (b7 <: i32) <: u32)
          (cast (b6 <: i32) <: u32)
          (cast (b5 <: i32) <: u32)
          (cast (b4 <: i32) <: u32)
          (cast (b3 <: i32) <: u32)
          (cast (b2 <: i32) <: u32)
          (cast (b1 <: i32) <: u32)
          (cast (b0 <: i32) <: u32)
        <:
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

let e___e_rw_mm256_permutevar8x32_epi32 = e___e_rw_mm256_permutevar8x32_epi32'

[@@ Minicore.Abstractions.Bitvec.v_REWRITE_RULE ]

assume
val e___e_rw_mm_shuffle_epi8':
    vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
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
  -> Lemma
    (ensures
      (e_mm_shuffle_epi8 vector
          (e_mm_set_epi8 e15 e14 e13 e12 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0
            <:
            Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128))
        <:
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)) ==
      (Minicore.Arch.X86.Extra.mm_shuffle_epi8_u8 vector (cast (e15 <: i8) <: u8)
          (cast (e14 <: i8) <: u8) (cast (e13 <: i8) <: u8) (cast (e12 <: i8) <: u8)
          (cast (e11 <: i8) <: u8) (cast (e10 <: i8) <: u8) (cast (e9 <: i8) <: u8)
          (cast (e8 <: i8) <: u8) (cast (e7 <: i8) <: u8) (cast (e6 <: i8) <: u8)
          (cast (e5 <: i8) <: u8) (cast (e4 <: i8) <: u8) (cast (e3 <: i8) <: u8)
          (cast (e2 <: i8) <: u8) (cast (e1 <: i8) <: u8) (cast (e0 <: i8) <: u8)
        <:
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)))

let e___e_rw_mm_shuffle_epi8 = e___e_rw_mm_shuffle_epi8'
