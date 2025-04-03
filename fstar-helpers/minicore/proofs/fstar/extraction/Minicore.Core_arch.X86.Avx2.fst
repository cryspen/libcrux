module Minicore.Core_arch.X86.Avx2
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
  Minicore.Abstractions.Bitvec.impl_10__chunked_shift (mk_u64 256)
    (mk_u64 16)
    (mk_u64 16)
    vector
    (Minicore.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
        #i128
        (fun temp_0_ ->
            let _:u64 = temp_0_ in
            cast (v_SHIFT_BY <: i32) <: i128)
      <:
      Minicore.Abstractions.Funarr.t_FunArray (mk_u64 16) i128)

let e_mm256_srli_epi64
      (v_SHIFT_BY: i32)
      (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Prims.Pure (Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (requires v_SHIFT_BY >=. mk_i32 0 && v_SHIFT_BY <. mk_i32 64)
      (fun _ -> Prims.l_True) =
  Minicore.Abstractions.Bitvec.impl_10__chunked_shift (mk_u64 256)
    (mk_u64 64)
    (mk_u64 4)
    vector
    (Minicore.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
        #i128
        (fun temp_0_ ->
            let _:u64 = temp_0_ in
            Core.Ops.Arith.f_neg (cast (v_SHIFT_BY <: i32) <: i128) <: i128)
      <:
      Minicore.Abstractions.Funarr.t_FunArray (mk_u64 4) i128)

assume
val e_mm256_mullo_epi16':
    e_vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    e_shifts: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let e_mm256_mullo_epi16 = e_mm256_mullo_epi16'

assume
val e_mm256_sllv_epi32':
    vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    counts: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let e_mm256_sllv_epi32 = e_mm256_sllv_epi32'

assume
val e_mm256_srlv_epi32':
    vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    counts: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let e_mm256_srlv_epi32 = e_mm256_srlv_epi32'

assume
val e_mm256_permutevar8x32_epi32':
    a: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let e_mm256_permutevar8x32_epi32 = e_mm256_permutevar8x32_epi32'

let e_mm256_extracti128_si256
      (v_IMM8: i32)
      (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Minicore.Abstractions.Bitvec.impl_9__from_fn (mk_u64 128)
    (fun i ->
        let i:u64 = i in
        vector.[ i +! (if v_IMM8 =. mk_i32 0 <: bool then mk_u64 0 else mk_u64 128) <: u64 ]
        <:
        Minicore.Abstractions.Bit.t_Bit)

assume
val e_mm256_shuffle_epi8':
    vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    indexes: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)

let e_mm256_shuffle_epi8 = e_mm256_shuffle_epi8'
