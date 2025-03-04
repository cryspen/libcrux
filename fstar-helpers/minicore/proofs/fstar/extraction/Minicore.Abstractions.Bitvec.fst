module Minicore.Abstractions.Bitvec
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Minicore.Abstractions.Bit in
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
type t_BitVec (v_N: usize) =
  | BitVec : Minicore.Abstractions.Funarr.t_FunArray v_N Minicore.Abstractions.Bit.t_Bit
    -> t_BitVec v_N

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': v_N: usize -> Core.Clone.t_Clone (t_BitVec v_N)

let impl_1 (v_N: usize) = impl_1' v_N

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl': v_N: usize -> Core.Marker.t_Copy (t_BitVec v_N)

let impl (v_N: usize) = impl' v_N

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': v_N: usize -> Core.Marker.t_StructuralPartialEq (t_BitVec v_N)

let impl_3 (v_N: usize) = impl_3' v_N

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_4': v_N: usize -> Core.Cmp.t_PartialEq (t_BitVec v_N) (t_BitVec v_N)

let impl_4 (v_N: usize) = impl_4' v_N

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': v_N: usize -> Core.Cmp.t_Eq (t_BitVec v_N)

let impl_2 (v_N: usize) = impl_2' v_N

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6 (v_N: usize) : Core.Ops.Index.t_Index (t_BitVec v_N) usize =
  {
    f_Output = Minicore.Abstractions.Bit.t_Bit;
    f_index_pre = (fun (self_: t_BitVec v_N) (index: usize) -> index <. v_N);
    f_index_post
    =
    (fun (self: t_BitVec v_N) (index: usize) (out: Minicore.Abstractions.Bit.t_Bit) -> true);
    f_index
    =
    fun (self: t_BitVec v_N) (index: usize) ->
      Minicore.Abstractions.Funarr.impl_6__get v_N #Minicore.Abstractions.Bit.t_Bit self._0 index
  }

/// Convert a fun array of bits into an unsigned number.
let math_int_from_fnarr_bit
      (v_N: usize)
      (bits: Minicore.Abstractions.Funarr.t_FunArray v_N Minicore.Abstractions.Bit.t_Bit)
    : Hax_lib.Int.t_Int =
  Minicore.Abstractions.Funarr.impl_6__fold v_N
    #Minicore.Abstractions.Bit.t_Bit
    #Hax_lib.Int.t_Int
    bits
    (0 <: Hax_lib.Int.t_Int)
    (fun acc n ->
        let acc:Hax_lib.Int.t_Int = acc in
        let n:Minicore.Abstractions.Bit.t_Bit = n in
        (acc * (2 <: Hax_lib.Int.t_Int) <: Hax_lib.Int.t_Int) +
        (Rust_primitives.Hax.Int.from_machine (Core.Convert.f_from #u8
                #Minicore.Abstractions.Bit.t_Bit
                #FStar.Tactics.Typeclasses.solve
                n
              <:
              u8)
          <:
          Hax_lib.Int.t_Int)
        <:
        Hax_lib.Int.t_Int)

/// Convert a bit slice into a machine integer of type `T`.
let int_from_fnarr_bit
      (v_N: usize)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Minicore.Abstractions.Bit.t_MachineInteger v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Marker.t_Copy v_T)
      (bits: Minicore.Abstractions.Funarr.t_FunArray v_N Minicore.Abstractions.Bit.t_Bit)
    : Prims.Pure Hax_lib.Int.t_Int
      (requires
        (Rust_primitives.Hax.Int.from_machine v_N <: Hax_lib.Int.t_Int) =
        (Rust_primitives.Hax.Int.from_machine (Minicore.Abstractions.Bit.f_bits #v_T
                #FStar.Tactics.Typeclasses.solve
                ()
              <:
              u32)
          <:
          Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert (v_N =.
            (cast (Minicore.Abstractions.Bit.f_bits #v_T #FStar.Tactics.Typeclasses.solve () <: u32)
              <:
              usize)
            <:
            bool)
      in
      ()
  in
  if Minicore.Abstractions.Bit.f_SIGNED #v_T #FStar.Tactics.Typeclasses.solve
  then
    let is_negative:bool =
      match
        bits.[ (cast (Minicore.Abstractions.Bit.f_bits #v_T #FStar.Tactics.Typeclasses.solve ()
                <:
                u32)
            <:
            usize) -!
          mk_usize 1
          <:
          usize ]
        <:
        Minicore.Abstractions.Bit.t_Bit
      with
      | Minicore.Abstractions.Bit.Bit_One  -> true
      | _ -> false
    in
    let s:Hax_lib.Int.t_Int =
      math_int_from_fnarr_bit v_N
        (Minicore.Abstractions.Funarr.impl_6__from_fn v_N
            #Minicore.Abstractions.Bit.t_Bit
            (fun i ->
                let i:usize = i in
                if i =. (v_N -! mk_usize 1 <: usize) <: bool
                then Minicore.Abstractions.Bit.Bit_Zero <: Minicore.Abstractions.Bit.t_Bit
                else bits.[ i ] <: Minicore.Abstractions.Bit.t_Bit)
          <:
          Minicore.Abstractions.Funarr.t_FunArray v_N Minicore.Abstractions.Bit.t_Bit)
    in
    if is_negative then (0 <: Hax_lib.Int.t_Int) - s else s
  else math_int_from_fnarr_bit v_N bits

let impl_7__from_fn
    (v_N: usize)
    (f: (i: usize {v i < v v_N}) -> Minicore.Abstractions.Bit.t_Bit)
    : t_BitVec v_N = 
    BitVec(Minicore.Abstractions.Funarr.impl_6__from_fn v_N f)
