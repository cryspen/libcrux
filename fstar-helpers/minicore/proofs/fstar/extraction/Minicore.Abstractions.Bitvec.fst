module Minicore.Abstractions.Bitvec
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Minicore.Abstractions.Funarr in
  ()

noeq

/// A fixed-size bit vector type.
/// `BitVec<N>` is a specification-friendly, fixed-length bit vector that internally
/// stores an array of [`Bit`] values, where each `Bit` represents a single binary digit (0 or 1).
/// This type provides several utility methods for constructing and converting bit vectors:
/// The [`Debug`] implementation for `BitVec` pretty-prints the bits in groups of eight,
/// making the bit pattern more human-readable. The type also implements indexing,
/// allowing for easy access to individual bits.
type t_BitVec (v_N: u64) =
  | BitVec : Minicore.Abstractions.Funarr.t_FunArray v_N Minicore.Abstractions.Bit.t_Bit
    -> t_BitVec v_N

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': v_N: u64 -> Core.Marker.t_StructuralPartialEq (t_BitVec v_N)

let impl_3 (v_N: u64) = impl_3' v_N

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_4': v_N: u64 -> Core.Cmp.t_PartialEq (t_BitVec v_N) (t_BitVec v_N)

let impl_4 (v_N: u64) = impl_4' v_N


[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6 (v_N: u64) : Core.Ops.Index.t_Index (t_BitVec v_N) u64 =
  {
    f_Output = Minicore.Abstractions.Bit.t_Bit;
    f_index_pre = (fun (self_: t_BitVec v_N) (index: u64) -> index <. v_N);
    f_index_post
    =
    (fun (self: t_BitVec v_N) (index: u64) (out: Minicore.Abstractions.Bit.t_Bit) -> true);
    f_index
    =
    fun (self: t_BitVec v_N) (index: u64) ->
      Minicore.Abstractions.Funarr.impl_5__get v_N #Minicore.Abstractions.Bit.t_Bit self._0 index
  }

let impl_9__from_fn
    (v_N: u64)
    (f: (i: u64 {v i < v v_N}) -> Minicore.Abstractions.Bit.t_Bit)
    : t_BitVec v_N = 
    BitVec(Minicore.Abstractions.Funarr.impl_5__from_fn v_N f)

let impl_7__pointwise (self: t_BitVec (mk_u64 128)) : t_BitVec (mk_u64 128) =
  impl_9__from_fn (mk_u64 128)
    (fun i ->
        let i:u64 = i in
        match i <: u64 with
        | Rust_primitives.Integers.MkInt 0 -> self.[ mk_u64 0 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 1 -> self.[ mk_u64 1 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 2 -> self.[ mk_u64 2 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 3 -> self.[ mk_u64 3 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 4 -> self.[ mk_u64 4 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 5 -> self.[ mk_u64 5 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 6 -> self.[ mk_u64 6 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 7 -> self.[ mk_u64 7 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 8 -> self.[ mk_u64 8 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 9 -> self.[ mk_u64 9 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 10 -> self.[ mk_u64 10 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 11 -> self.[ mk_u64 11 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 12 -> self.[ mk_u64 12 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 13 -> self.[ mk_u64 13 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 14 -> self.[ mk_u64 14 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 15 -> self.[ mk_u64 15 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 16 -> self.[ mk_u64 16 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 17 -> self.[ mk_u64 17 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 18 -> self.[ mk_u64 18 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 19 -> self.[ mk_u64 19 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 20 -> self.[ mk_u64 20 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 21 -> self.[ mk_u64 21 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 22 -> self.[ mk_u64 22 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 23 -> self.[ mk_u64 23 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 24 -> self.[ mk_u64 24 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 25 -> self.[ mk_u64 25 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 26 -> self.[ mk_u64 26 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 27 -> self.[ mk_u64 27 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 28 -> self.[ mk_u64 28 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 29 -> self.[ mk_u64 29 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 30 -> self.[ mk_u64 30 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 31 -> self.[ mk_u64 31 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 32 -> self.[ mk_u64 32 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 33 -> self.[ mk_u64 33 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 34 -> self.[ mk_u64 34 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 35 -> self.[ mk_u64 35 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 36 -> self.[ mk_u64 36 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 37 -> self.[ mk_u64 37 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 38 -> self.[ mk_u64 38 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 39 -> self.[ mk_u64 39 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 40 -> self.[ mk_u64 40 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 41 -> self.[ mk_u64 41 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 42 -> self.[ mk_u64 42 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 43 -> self.[ mk_u64 43 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 44 -> self.[ mk_u64 44 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 45 -> self.[ mk_u64 45 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 46 -> self.[ mk_u64 46 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 47 -> self.[ mk_u64 47 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 48 -> self.[ mk_u64 48 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 49 -> self.[ mk_u64 49 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 50 -> self.[ mk_u64 50 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 51 -> self.[ mk_u64 51 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 52 -> self.[ mk_u64 52 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 53 -> self.[ mk_u64 53 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 54 -> self.[ mk_u64 54 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 55 -> self.[ mk_u64 55 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 56 -> self.[ mk_u64 56 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 57 -> self.[ mk_u64 57 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 58 -> self.[ mk_u64 58 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 59 -> self.[ mk_u64 59 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 60 -> self.[ mk_u64 60 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 61 -> self.[ mk_u64 61 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 62 -> self.[ mk_u64 62 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 63 -> self.[ mk_u64 63 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 64 -> self.[ mk_u64 64 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 65 -> self.[ mk_u64 65 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 66 -> self.[ mk_u64 66 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 67 -> self.[ mk_u64 67 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 68 -> self.[ mk_u64 68 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 69 -> self.[ mk_u64 69 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 70 -> self.[ mk_u64 70 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 71 -> self.[ mk_u64 71 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 72 -> self.[ mk_u64 72 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 73 -> self.[ mk_u64 73 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 74 -> self.[ mk_u64 74 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 75 -> self.[ mk_u64 75 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 76 -> self.[ mk_u64 76 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 77 -> self.[ mk_u64 77 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 78 -> self.[ mk_u64 78 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 79 -> self.[ mk_u64 79 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 80 -> self.[ mk_u64 80 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 81 -> self.[ mk_u64 81 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 82 -> self.[ mk_u64 82 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 83 -> self.[ mk_u64 83 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 84 -> self.[ mk_u64 84 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 85 -> self.[ mk_u64 85 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 86 -> self.[ mk_u64 86 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 87 -> self.[ mk_u64 87 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 88 -> self.[ mk_u64 88 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 89 -> self.[ mk_u64 89 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 90 -> self.[ mk_u64 90 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 91 -> self.[ mk_u64 91 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 92 -> self.[ mk_u64 92 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 93 -> self.[ mk_u64 93 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 94 -> self.[ mk_u64 94 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 95 -> self.[ mk_u64 95 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 96 -> self.[ mk_u64 96 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 97 -> self.[ mk_u64 97 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 98 -> self.[ mk_u64 98 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 99 -> self.[ mk_u64 99 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 100 ->
          self.[ mk_u64 100 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 101 ->
          self.[ mk_u64 101 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 102 ->
          self.[ mk_u64 102 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 103 ->
          self.[ mk_u64 103 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 104 ->
          self.[ mk_u64 104 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 105 ->
          self.[ mk_u64 105 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 106 ->
          self.[ mk_u64 106 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 107 ->
          self.[ mk_u64 107 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 108 ->
          self.[ mk_u64 108 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 109 ->
          self.[ mk_u64 109 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 110 ->
          self.[ mk_u64 110 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 111 ->
          self.[ mk_u64 111 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 112 ->
          self.[ mk_u64 112 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 113 ->
          self.[ mk_u64 113 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 114 ->
          self.[ mk_u64 114 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 115 ->
          self.[ mk_u64 115 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 116 ->
          self.[ mk_u64 116 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 117 ->
          self.[ mk_u64 117 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 118 ->
          self.[ mk_u64 118 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 119 ->
          self.[ mk_u64 119 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 120 ->
          self.[ mk_u64 120 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 121 ->
          self.[ mk_u64 121 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 122 ->
          self.[ mk_u64 122 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 123 ->
          self.[ mk_u64 123 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 124 ->
          self.[ mk_u64 124 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 125 ->
          self.[ mk_u64 125 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 126 ->
          self.[ mk_u64 126 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 127 ->
          self.[ mk_u64 127 ] <: Minicore.Abstractions.Bit.t_Bit
        | _ ->
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

              <:
              Rust_primitives.Hax.t_Never)
          <:
          Minicore.Abstractions.Bit.t_Bit)

let impl_8__pointwise (self: t_BitVec (mk_u64 256)) : t_BitVec (mk_u64 256) =
  impl_9__from_fn (mk_u64 256)
    (fun i ->
        let i:u64 = i in
        match i <: u64 with
        | Rust_primitives.Integers.MkInt 0 -> self.[ mk_u64 0 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 1 -> self.[ mk_u64 1 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 2 -> self.[ mk_u64 2 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 3 -> self.[ mk_u64 3 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 4 -> self.[ mk_u64 4 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 5 -> self.[ mk_u64 5 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 6 -> self.[ mk_u64 6 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 7 -> self.[ mk_u64 7 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 8 -> self.[ mk_u64 8 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 9 -> self.[ mk_u64 9 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 10 -> self.[ mk_u64 10 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 11 -> self.[ mk_u64 11 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 12 -> self.[ mk_u64 12 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 13 -> self.[ mk_u64 13 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 14 -> self.[ mk_u64 14 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 15 -> self.[ mk_u64 15 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 16 -> self.[ mk_u64 16 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 17 -> self.[ mk_u64 17 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 18 -> self.[ mk_u64 18 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 19 -> self.[ mk_u64 19 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 20 -> self.[ mk_u64 20 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 21 -> self.[ mk_u64 21 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 22 -> self.[ mk_u64 22 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 23 -> self.[ mk_u64 23 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 24 -> self.[ mk_u64 24 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 25 -> self.[ mk_u64 25 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 26 -> self.[ mk_u64 26 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 27 -> self.[ mk_u64 27 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 28 -> self.[ mk_u64 28 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 29 -> self.[ mk_u64 29 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 30 -> self.[ mk_u64 30 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 31 -> self.[ mk_u64 31 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 32 -> self.[ mk_u64 32 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 33 -> self.[ mk_u64 33 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 34 -> self.[ mk_u64 34 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 35 -> self.[ mk_u64 35 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 36 -> self.[ mk_u64 36 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 37 -> self.[ mk_u64 37 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 38 -> self.[ mk_u64 38 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 39 -> self.[ mk_u64 39 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 40 -> self.[ mk_u64 40 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 41 -> self.[ mk_u64 41 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 42 -> self.[ mk_u64 42 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 43 -> self.[ mk_u64 43 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 44 -> self.[ mk_u64 44 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 45 -> self.[ mk_u64 45 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 46 -> self.[ mk_u64 46 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 47 -> self.[ mk_u64 47 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 48 -> self.[ mk_u64 48 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 49 -> self.[ mk_u64 49 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 50 -> self.[ mk_u64 50 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 51 -> self.[ mk_u64 51 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 52 -> self.[ mk_u64 52 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 53 -> self.[ mk_u64 53 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 54 -> self.[ mk_u64 54 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 55 -> self.[ mk_u64 55 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 56 -> self.[ mk_u64 56 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 57 -> self.[ mk_u64 57 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 58 -> self.[ mk_u64 58 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 59 -> self.[ mk_u64 59 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 60 -> self.[ mk_u64 60 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 61 -> self.[ mk_u64 61 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 62 -> self.[ mk_u64 62 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 63 -> self.[ mk_u64 63 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 64 -> self.[ mk_u64 64 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 65 -> self.[ mk_u64 65 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 66 -> self.[ mk_u64 66 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 67 -> self.[ mk_u64 67 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 68 -> self.[ mk_u64 68 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 69 -> self.[ mk_u64 69 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 70 -> self.[ mk_u64 70 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 71 -> self.[ mk_u64 71 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 72 -> self.[ mk_u64 72 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 73 -> self.[ mk_u64 73 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 74 -> self.[ mk_u64 74 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 75 -> self.[ mk_u64 75 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 76 -> self.[ mk_u64 76 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 77 -> self.[ mk_u64 77 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 78 -> self.[ mk_u64 78 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 79 -> self.[ mk_u64 79 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 80 -> self.[ mk_u64 80 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 81 -> self.[ mk_u64 81 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 82 -> self.[ mk_u64 82 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 83 -> self.[ mk_u64 83 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 84 -> self.[ mk_u64 84 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 85 -> self.[ mk_u64 85 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 86 -> self.[ mk_u64 86 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 87 -> self.[ mk_u64 87 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 88 -> self.[ mk_u64 88 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 89 -> self.[ mk_u64 89 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 90 -> self.[ mk_u64 90 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 91 -> self.[ mk_u64 91 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 92 -> self.[ mk_u64 92 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 93 -> self.[ mk_u64 93 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 94 -> self.[ mk_u64 94 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 95 -> self.[ mk_u64 95 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 96 -> self.[ mk_u64 96 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 97 -> self.[ mk_u64 97 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 98 -> self.[ mk_u64 98 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 99 -> self.[ mk_u64 99 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 100 ->
          self.[ mk_u64 100 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 101 ->
          self.[ mk_u64 101 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 102 ->
          self.[ mk_u64 102 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 103 ->
          self.[ mk_u64 103 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 104 ->
          self.[ mk_u64 104 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 105 ->
          self.[ mk_u64 105 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 106 ->
          self.[ mk_u64 106 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 107 ->
          self.[ mk_u64 107 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 108 ->
          self.[ mk_u64 108 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 109 ->
          self.[ mk_u64 109 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 110 ->
          self.[ mk_u64 110 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 111 ->
          self.[ mk_u64 111 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 112 ->
          self.[ mk_u64 112 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 113 ->
          self.[ mk_u64 113 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 114 ->
          self.[ mk_u64 114 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 115 ->
          self.[ mk_u64 115 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 116 ->
          self.[ mk_u64 116 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 117 ->
          self.[ mk_u64 117 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 118 ->
          self.[ mk_u64 118 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 119 ->
          self.[ mk_u64 119 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 120 ->
          self.[ mk_u64 120 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 121 ->
          self.[ mk_u64 121 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 122 ->
          self.[ mk_u64 122 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 123 ->
          self.[ mk_u64 123 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 124 ->
          self.[ mk_u64 124 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 125 ->
          self.[ mk_u64 125 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 126 ->
          self.[ mk_u64 126 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 127 ->
          self.[ mk_u64 127 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 128 ->
          self.[ mk_u64 128 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 129 ->
          self.[ mk_u64 129 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 130 ->
          self.[ mk_u64 130 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 131 ->
          self.[ mk_u64 131 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 132 ->
          self.[ mk_u64 132 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 133 ->
          self.[ mk_u64 133 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 134 ->
          self.[ mk_u64 134 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 135 ->
          self.[ mk_u64 135 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 136 ->
          self.[ mk_u64 136 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 137 ->
          self.[ mk_u64 137 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 138 ->
          self.[ mk_u64 138 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 139 ->
          self.[ mk_u64 139 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 140 ->
          self.[ mk_u64 140 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 141 ->
          self.[ mk_u64 141 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 142 ->
          self.[ mk_u64 142 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 143 ->
          self.[ mk_u64 143 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 144 ->
          self.[ mk_u64 144 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 145 ->
          self.[ mk_u64 145 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 146 ->
          self.[ mk_u64 146 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 147 ->
          self.[ mk_u64 147 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 148 ->
          self.[ mk_u64 148 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 149 ->
          self.[ mk_u64 149 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 150 ->
          self.[ mk_u64 150 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 151 ->
          self.[ mk_u64 151 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 152 ->
          self.[ mk_u64 152 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 153 ->
          self.[ mk_u64 153 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 154 ->
          self.[ mk_u64 154 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 155 ->
          self.[ mk_u64 155 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 156 ->
          self.[ mk_u64 156 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 157 ->
          self.[ mk_u64 157 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 158 ->
          self.[ mk_u64 158 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 159 ->
          self.[ mk_u64 159 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 160 ->
          self.[ mk_u64 160 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 161 ->
          self.[ mk_u64 161 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 162 ->
          self.[ mk_u64 162 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 163 ->
          self.[ mk_u64 163 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 164 ->
          self.[ mk_u64 164 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 165 ->
          self.[ mk_u64 165 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 166 ->
          self.[ mk_u64 166 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 167 ->
          self.[ mk_u64 167 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 168 ->
          self.[ mk_u64 168 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 169 ->
          self.[ mk_u64 169 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 170 ->
          self.[ mk_u64 170 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 171 ->
          self.[ mk_u64 171 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 172 ->
          self.[ mk_u64 172 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 173 ->
          self.[ mk_u64 173 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 174 ->
          self.[ mk_u64 174 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 175 ->
          self.[ mk_u64 175 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 176 ->
          self.[ mk_u64 176 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 177 ->
          self.[ mk_u64 177 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 178 ->
          self.[ mk_u64 178 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 179 ->
          self.[ mk_u64 179 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 180 ->
          self.[ mk_u64 180 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 181 ->
          self.[ mk_u64 181 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 182 ->
          self.[ mk_u64 182 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 183 ->
          self.[ mk_u64 183 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 184 ->
          self.[ mk_u64 184 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 185 ->
          self.[ mk_u64 185 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 186 ->
          self.[ mk_u64 186 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 187 ->
          self.[ mk_u64 187 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 188 ->
          self.[ mk_u64 188 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 189 ->
          self.[ mk_u64 189 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 190 ->
          self.[ mk_u64 190 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 191 ->
          self.[ mk_u64 191 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 192 ->
          self.[ mk_u64 192 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 193 ->
          self.[ mk_u64 193 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 194 ->
          self.[ mk_u64 194 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 195 ->
          self.[ mk_u64 195 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 196 ->
          self.[ mk_u64 196 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 197 ->
          self.[ mk_u64 197 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 198 ->
          self.[ mk_u64 198 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 199 ->
          self.[ mk_u64 199 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 200 ->
          self.[ mk_u64 200 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 201 ->
          self.[ mk_u64 201 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 202 ->
          self.[ mk_u64 202 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 203 ->
          self.[ mk_u64 203 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 204 ->
          self.[ mk_u64 204 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 205 ->
          self.[ mk_u64 205 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 206 ->
          self.[ mk_u64 206 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 207 ->
          self.[ mk_u64 207 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 208 ->
          self.[ mk_u64 208 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 209 ->
          self.[ mk_u64 209 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 210 ->
          self.[ mk_u64 210 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 211 ->
          self.[ mk_u64 211 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 212 ->
          self.[ mk_u64 212 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 213 ->
          self.[ mk_u64 213 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 214 ->
          self.[ mk_u64 214 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 215 ->
          self.[ mk_u64 215 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 216 ->
          self.[ mk_u64 216 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 217 ->
          self.[ mk_u64 217 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 218 ->
          self.[ mk_u64 218 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 219 ->
          self.[ mk_u64 219 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 220 ->
          self.[ mk_u64 220 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 221 ->
          self.[ mk_u64 221 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 222 ->
          self.[ mk_u64 222 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 223 ->
          self.[ mk_u64 223 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 224 ->
          self.[ mk_u64 224 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 225 ->
          self.[ mk_u64 225 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 226 ->
          self.[ mk_u64 226 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 227 ->
          self.[ mk_u64 227 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 228 ->
          self.[ mk_u64 228 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 229 ->
          self.[ mk_u64 229 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 230 ->
          self.[ mk_u64 230 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 231 ->
          self.[ mk_u64 231 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 232 ->
          self.[ mk_u64 232 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 233 ->
          self.[ mk_u64 233 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 234 ->
          self.[ mk_u64 234 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 235 ->
          self.[ mk_u64 235 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 236 ->
          self.[ mk_u64 236 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 237 ->
          self.[ mk_u64 237 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 238 ->
          self.[ mk_u64 238 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 239 ->
          self.[ mk_u64 239 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 240 ->
          self.[ mk_u64 240 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 241 ->
          self.[ mk_u64 241 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 242 ->
          self.[ mk_u64 242 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 243 ->
          self.[ mk_u64 243 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 244 ->
          self.[ mk_u64 244 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 245 ->
          self.[ mk_u64 245 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 246 ->
          self.[ mk_u64 246 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 247 ->
          self.[ mk_u64 247 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 248 ->
          self.[ mk_u64 248 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 249 ->
          self.[ mk_u64 249 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 250 ->
          self.[ mk_u64 250 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 251 ->
          self.[ mk_u64 251 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 252 ->
          self.[ mk_u64 252 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 253 ->
          self.[ mk_u64 253 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 254 ->
          self.[ mk_u64 254 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 255 ->
          self.[ mk_u64 255 ] <: Minicore.Abstractions.Bit.t_Bit
        | _ ->
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

              <:
              Rust_primitives.Hax.t_Never)
          <:
          Minicore.Abstractions.Bit.t_Bit)

/// An F* attribute that indiquates a rewritting lemma should be applied
let v_REWRITE_RULE: Prims.unit = ()

open FStar.FunctionalExtensionality

let extensionality' (#a: Type) (#b: Type) (f g: FStar.FunctionalExtensionality.(a ^-> b))
  : Lemma (ensures (FStar.FunctionalExtensionality.feq f g <==> f == g))
  = ()

let mark_to_normalize #t (x: t): t = x

open FStar.Tactics.V2
#push-options "--z3rlimit 80 --admit_smt_queries true"
let bitvec_rewrite_lemma_128 (x: t_BitVec (mk_u64 128))
: Lemma (x == mark_to_normalize (impl_7__pointwise x)) =
    let a = x._0 in
    let b = (impl_7__pointwise x)._0 in
    assert_norm (FStar.FunctionalExtensionality.feq a b);
    extensionality' a b

let bitvec_rewrite_lemma_256 (x: t_BitVec (mk_u64 256))
: Lemma (x == mark_to_normalize (impl_8__pointwise x)) =
    let a = x._0 in
    let b = (impl_8__pointwise x)._0 in
    assert_norm (FStar.FunctionalExtensionality.feq a b);
    extensionality' a b

let funarr_rewrite_lemma_16 #t (x: Minicore.Abstractions.Funarr.t_FunArray _ t): Lemma (x == mark_to_normalize (Minicore.Abstractions.Funarr.impl_8__pointwise x)) = admit ()
let funarr_rewrite_lemma_8 #t (x: Minicore.Abstractions.Funarr.t_FunArray _ t): Lemma (x == mark_to_normalize (Minicore.Abstractions.Funarr.impl_7__pointwise x)) = admit ()
let funarr_rewrite_lemma_4 #t (x: Minicore.Abstractions.Funarr.t_FunArray _ t): Lemma (x == mark_to_normalize (Minicore.Abstractions.Funarr.impl_6__pointwise x)) = admit ()
#pop-options

let bitvec_postprocess_norm (): Tac unit = with_compat_pre_core 1 (fun () ->
    let debug_mode = ext_enabled "debug_bv_postprocess_rewrite" in
    let crate = match cur_module () with | crate::_ -> crate | _ -> fail "Empty module name" in
    // Remove indirections
    // norm [primops; iota; delta_namespace [crate; "Libcrux_intrinsics"]; zeta_full];
    // Rewrite call chains
    // let lemmas = FStar.List.Tot.map (fun f -> pack_ln (FStar.Stubs.Reflection.V2.Data.Tv_FVar f)) (lookup_attr (`v_REWRITE_RULE) (top_env ())) in
    // l_to_r lemmas;
    /// Get rid of casts
    // norm [primops; iota; delta_namespace ["Rust_primitives"; "Prims.pow2"]; zeta_full];
    // if debug_mode then print ("[postprocess_rewrite_helper] lemmas = " ^ term_to_string (quote lemmas));

    l_to_r [`funarr_rewrite_lemma_16; `funarr_rewrite_lemma_8; `funarr_rewrite_lemma_4];
    // l_to_r [`bitvec_rewrite_lemma_128; `bitvec_rewrite_lemma_256; `funarr_rewrite_lemma_16; `funarr_rewrite_lemma_8; `funarr_rewrite_lemma_4];

    let round _: Tac unit =
        if debug_mode then dump "[postprocess_rewrite_helper] Rewrote goal";
        // Normalize as much as possible
        norm [primops; iota; delta_namespace ["Core"; crate; "Minicore"; "Libcrux_intrinsics"; "FStar.FunctionalExtensionality"; "Rust_primitives"]; zeta_full];
        if debug_mode then print ("[postprocess_rewrite_helper] first norm done");
        // Compute the last bits
        // compute ();
        // if debug_mode then dump ("[postprocess_rewrite_helper] compute done");
        // Force full normalization
        norm [primops; iota; delta; unascribe; zeta_full];
        if debug_mode then dump "[postprocess_rewrite_helper] after full normalization";
        // Solves the goal `<normalized body> == ?u`
        trefl ()
    in

    ctrl_rewrite BottomUp (fun t ->
        let f, args = collect_app t in
        let matches = match inspect f with | Tv_UInst f _ | Tv_FVar f -> (inspect_fv f) = explode_qn (`%mark_to_normalize) | _ -> false in
        let has_two_args = match args with | [_; _] -> true | _ -> false in
        (matches && has_two_args, Continue)
    ) round;

    // Solves the goal `<normalized body> == ?u`
    trefl ()
)

#push-options "--z3rlimit 50 --split_queries always"

let impl_10__chunked_shift__chunked_shift
      (v_N v_CHUNK v_SHIFTS: u64)
      (bitvec: t_BitVec v_N)
      (shl: Minicore.Abstractions.Funarr.t_FunArray v_SHIFTS i128)
    : Prims.Pure (t_BitVec v_N)
      (requires
        v_CHUNK >. mk_u64 0 &&
        ((Rust_primitives.Hax.Int.from_machine v_CHUNK <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine v_SHIFTS <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) =
        (Rust_primitives.Hax.Int.from_machine v_N <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  impl_9__from_fn v_N
    (fun i ->
        let i:u64 = i in
        let nth_bit:u64 = i %! v_CHUNK in
        let nth_chunk:u64 = i /! v_CHUNK in
        let _:Prims.unit =
          Hax_lib.assert_prop (b2t
              ((Rust_primitives.Hax.Int.from_machine nth_chunk <: Hax_lib.Int.t_Int) <=
                ((Rust_primitives.Hax.Int.from_machine v_SHIFTS <: Hax_lib.Int.t_Int) -
                  (1 <: Hax_lib.Int.t_Int)
                  <:
                  Hax_lib.Int.t_Int)
                <:
                bool))
        in
        let _:Prims.unit = () in
        let _:Prims.unit =
          Hax_lib.assert_prop (b2t
              (((Rust_primitives.Hax.Int.from_machine nth_chunk <: Hax_lib.Int.t_Int) *
                  (Rust_primitives.Hax.Int.from_machine v_CHUNK <: Hax_lib.Int.t_Int)
                  <:
                  Hax_lib.Int.t_Int) <=
                (((Rust_primitives.Hax.Int.from_machine v_SHIFTS <: Hax_lib.Int.t_Int) -
                    (1 <: Hax_lib.Int.t_Int)
                    <:
                    Hax_lib.Int.t_Int) *
                  (Rust_primitives.Hax.Int.from_machine v_CHUNK <: Hax_lib.Int.t_Int)
                  <:
                  Hax_lib.Int.t_Int)
                <:
                bool))
        in
        let _:Prims.unit = () in
        let (shift: i128):i128 = if nth_chunk <. v_SHIFTS then shl.[ nth_chunk ] else mk_i128 0 in
        let local_index:i128 =
          Core.Num.impl_i128__wrapping_sub (cast (nth_bit <: u64) <: i128) shift
        in
        if local_index <. (cast (v_CHUNK <: u64) <: i128) && local_index >=. mk_i128 0
        then
          let local_index:u64 = cast (local_index <: i128) <: u64 in
          let _:Prims.unit =
            Hax_lib.assert_prop (b2t
                ((((Rust_primitives.Hax.Int.from_machine nth_chunk <: Hax_lib.Int.t_Int) *
                      (Rust_primitives.Hax.Int.from_machine v_CHUNK <: Hax_lib.Int.t_Int)
                      <:
                      Hax_lib.Int.t_Int) +
                    (Rust_primitives.Hax.Int.from_machine local_index <: Hax_lib.Int.t_Int)
                    <:
                    Hax_lib.Int.t_Int) <
                  ((Rust_primitives.Hax.Int.from_machine v_SHIFTS <: Hax_lib.Int.t_Int) *
                    (Rust_primitives.Hax.Int.from_machine v_CHUNK <: Hax_lib.Int.t_Int)
                    <:
                    Hax_lib.Int.t_Int)
                  <:
                  bool))
          in
          let _:Prims.unit = () in
          bitvec.[ (nth_chunk *! v_CHUNK <: u64) +! local_index <: u64 ]
        else Minicore.Abstractions.Bit.Bit_Zero <: Minicore.Abstractions.Bit.t_Bit)

#pop-options

let impl_10__chunked_shift
      (v_N v_CHUNK v_SHIFTS: u64)
      (self: t_BitVec v_N)
      (shl: Minicore.Abstractions.Funarr.t_FunArray v_SHIFTS i128)
    : Prims.Pure (t_BitVec v_N)
      (requires
        v_CHUNK >. mk_u64 0 &&
        ((Rust_primitives.Hax.Int.from_machine v_CHUNK <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine v_SHIFTS <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) =
        (Rust_primitives.Hax.Int.from_machine v_N <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = impl_10__chunked_shift__chunked_shift v_N v_CHUNK v_SHIFTS self shl
