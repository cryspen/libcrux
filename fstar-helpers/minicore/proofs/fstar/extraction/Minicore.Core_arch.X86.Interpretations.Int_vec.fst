module Minicore.Core_arch.X86.Interpretations.Int_vec
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Minicore.Abstractions.Funarr in
  ()

let e_mm256_set1_epi32 (x: i32) : Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  Minicore.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        x)

let e_mm256_mul_epi32 (x y: Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    : Minicore.Abstractions.Funarr.t_FunArray (mk_u64 4) i64 =
  Minicore.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
    #i64
    (fun i ->
        let i:u64 = i in
        (cast (x.[ i *! mk_u64 2 <: u64 ] <: i32) <: i64) *!
        (cast (y.[ i *! mk_u64 2 <: u64 ] <: i32) <: i64)
        <:
        i64)

let e_mm256_sub_epi32 (x y: Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    : Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  Minicore.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun i ->
        let i:u64 = i in
        cast ((cast (x.[ i ] <: i32) <: i64) -! (cast (y.[ i ] <: i32) <: i64) <: i64) <: i32)

let e_mm256_shuffle_epi32
      (v_CONTROL: i32)
      (x: Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    : Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  let (indexes: Minicore.Abstractions.Funarr.t_FunArray (mk_u64 4) u64):Minicore.Abstractions.Funarr.t_FunArray
    (mk_u64 4) u64 =
    Minicore.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
      #u64
      (fun i ->
          let i:u64 = i in
          cast ((v_CONTROL >>! (i *! mk_u64 2 <: u64) <: i32) %! mk_i32 4 <: i32) <: u64)
  in
  Minicore.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun i ->
        let i:u64 = i in
        if i <. mk_u64 4 <: bool
        then x.[ indexes.[ i ] <: u64 ] <: i32
        else x.[ mk_u64 4 +! (indexes.[ i -! mk_u64 4 <: u64 ] <: u64) <: u64 ] <: i32)

let e_mm256_blend_epi32
      (v_CONTROL: i32)
      (x y: Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    : Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  Minicore.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun i ->
        let i:u64 = i in
        if ((v_CONTROL >>! i <: i32) %! mk_i32 2 <: i32) =. mk_i32 0 <: bool
        then x.[ i ] <: i32
        else y.[ i ] <: i32)
