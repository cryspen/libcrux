module Minicore.Arch.X86.Extra
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Minicore.Abstractions.Bitvec in
  let open Minicore.Abstractions.Funarr in
  ()

let mm256_sllv_epi32_u32_array
      (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_usize 256))
      (counts: Minicore.Abstractions.Funarr.t_FunArray (mk_usize 8) u32)
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_usize 256) =
  Minicore.Abstractions.Bitvec.impl_7__from_fn (mk_usize 256)
    (fun i ->
        let i:usize = i in
        let nth_bit:usize = i %! mk_usize 32 in
        let shift:u32 = counts.[ i /! mk_usize 32 <: usize ] in
        if (cast (nth_bit <: usize) <: i128) >=. (cast (shift <: u32) <: i128)
        then vector.[ i -! (cast (shift <: u32) <: usize) <: usize ]
        else Minicore.Abstractions.Bit.Bit_Zero <: Minicore.Abstractions.Bit.t_Bit)

let mm256_sllv_epi32_u32
      (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_usize 256))
      (b7 b6 b5 b4 b3 b2 b1 b0: u32)
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_usize 256) =
  mm256_sllv_epi32_u32_array vector
    (Minicore.Abstractions.Funarr.impl_6__from_fn (mk_usize 8)
        #u32
        (fun i ->
            let i:usize = i in
            match i <: usize with
            | Rust_primitives.Integers.MkInt 0 -> b7
            | Rust_primitives.Integers.MkInt 1 -> b6
            | Rust_primitives.Integers.MkInt 2 -> b5
            | Rust_primitives.Integers.MkInt 3 -> b4
            | Rust_primitives.Integers.MkInt 4 -> b3
            | Rust_primitives.Integers.MkInt 5 -> b2
            | Rust_primitives.Integers.MkInt 6 -> b1
            | Rust_primitives.Integers.MkInt 7 -> b0
            | _ ->
              Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

                  <:
                  Rust_primitives.Hax.t_Never)
              <:
              u32)
      <:
      Minicore.Abstractions.Funarr.t_FunArray (mk_usize 8) u32)

let mm256_permutevar8x32_epi32_u32_array
      (a: Minicore.Abstractions.Bitvec.t_BitVec (mk_usize 256))
      (b: Minicore.Abstractions.Funarr.t_FunArray (mk_usize 8) u32)
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_usize 256) =
  Minicore.Abstractions.Bitvec.impl_7__from_fn (mk_usize 256)
    (fun i ->
        let i:usize = i in
        let j:usize = i /! mk_usize 32 in
        let index:usize = (cast ((b.[ j ] <: u32) %! mk_u32 7 <: u32) <: usize) *! mk_usize 32 in
        a.[ index +! (i %! mk_usize 32 <: usize) <: usize ])

let mm256_permutevar8x32_epi32_u32
      (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_usize 256))
      (b7 b6 b5 b4 b3 b2 b1 b0: u32)
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_usize 256) =
  mm256_permutevar8x32_epi32_u32_array vector
    (Minicore.Abstractions.Funarr.impl_6__from_fn (mk_usize 8)
        #u32
        (fun i ->
            let i:usize = i in
            match i <: usize with
            | Rust_primitives.Integers.MkInt 0 -> b7
            | Rust_primitives.Integers.MkInt 1 -> b6
            | Rust_primitives.Integers.MkInt 2 -> b5
            | Rust_primitives.Integers.MkInt 3 -> b4
            | Rust_primitives.Integers.MkInt 4 -> b3
            | Rust_primitives.Integers.MkInt 5 -> b2
            | Rust_primitives.Integers.MkInt 6 -> b1
            | Rust_primitives.Integers.MkInt 7 -> b0
            | _ ->
              Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

                  <:
                  Rust_primitives.Hax.t_Never)
              <:
              u32)
      <:
      Minicore.Abstractions.Funarr.t_FunArray (mk_usize 8) u32)

let mm_shuffle_epi8_u8_array
      (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_usize 128))
      (indexes: Minicore.Abstractions.Funarr.t_FunArray (mk_usize 16) u8)
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_usize 128) =
  Minicore.Abstractions.Bitvec.impl_7__from_fn (mk_usize 128)
    (fun i ->
        let i:usize = i in
        let nth:usize = i /! mk_usize 8 in
        let index:u8 = indexes.[ nth ] in
        if index >. mk_u8 127
        then Minicore.Abstractions.Bit.Bit_Zero <: Minicore.Abstractions.Bit.t_Bit
        else
          let index:usize = cast (index %! mk_u8 15 <: u8) <: usize in
          vector.[ (index *! mk_usize 8 <: usize) +! (i %! mk_usize 8 <: usize) <: usize ])

let mm_shuffle_epi8_u8
      (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_usize 128))
      (b15 b14 b13 b12 b11 b10 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0: u8)
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_usize 128) =
  let indexes:Minicore.Abstractions.Funarr.t_FunArray (mk_usize 16) u8 =
    Minicore.Abstractions.Funarr.impl_6__from_fn (mk_usize 16)
      #u8
      (fun i ->
          let i:usize = i in
          match i <: usize with
          | Rust_primitives.Integers.MkInt 0 -> b15
          | Rust_primitives.Integers.MkInt 1 -> b14
          | Rust_primitives.Integers.MkInt 2 -> b13
          | Rust_primitives.Integers.MkInt 3 -> b12
          | Rust_primitives.Integers.MkInt 4 -> b11
          | Rust_primitives.Integers.MkInt 5 -> b10
          | Rust_primitives.Integers.MkInt 6 -> b9
          | Rust_primitives.Integers.MkInt 7 -> b8
          | Rust_primitives.Integers.MkInt 8 -> b7
          | Rust_primitives.Integers.MkInt 9 -> b6
          | Rust_primitives.Integers.MkInt 10 -> b5
          | Rust_primitives.Integers.MkInt 11 -> b4
          | Rust_primitives.Integers.MkInt 12 -> b3
          | Rust_primitives.Integers.MkInt 13 -> b2
          | Rust_primitives.Integers.MkInt 14 -> b1
          | Rust_primitives.Integers.MkInt 15 -> b0
          | _ ->
            Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

                <:
                Rust_primitives.Hax.t_Never)
            <:
            u8)
  in
  mm_shuffle_epi8_u8_array vector indexes
