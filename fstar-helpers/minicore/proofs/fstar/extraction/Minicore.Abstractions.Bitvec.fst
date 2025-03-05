module Minicore.Abstractions.Bitvec
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

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
val impl_1': v_N: u64 -> Core.Clone.t_Clone (t_BitVec v_N)

let impl_1 (v_N: u64) = impl_1' v_N

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl': v_N: u64 -> Core.Marker.t_Copy (t_BitVec v_N)

let impl (v_N: u64) = impl' v_N

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': v_N: u64 -> Core.Marker.t_StructuralPartialEq (t_BitVec v_N)

let impl_3 (v_N: u64) = impl_3' v_N

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_4': v_N: u64 -> Core.Cmp.t_PartialEq (t_BitVec v_N) (t_BitVec v_N)

let impl_4 (v_N: u64) = impl_4' v_N

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': v_N: u64 -> Core.Cmp.t_Eq (t_BitVec v_N)

let impl_2 (v_N: u64) = impl_2' v_N

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

let impl_7__from_fn
    (v_N: u64)
    (f: (i: u64 {v i < v v_N}) -> Minicore.Abstractions.Bit.t_Bit)
    : t_BitVec v_N = 
    BitVec(Minicore.Abstractions.Funarr.impl_5__from_fn v_N f)
