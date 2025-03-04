module Minicore.Abstractions.Bit
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// Represent a bit: `0` or `1`.
type t_Bit =
  | Bit_Zero : t_Bit
  | Bit_One : t_Bit

let t_Bit_cast_to_repr (x: t_Bit) : isize =
  match x <: t_Bit with
  | Bit_Zero  -> mk_isize 0
  | Bit_One  -> mk_isize 1

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': Core.Clone.t_Clone t_Bit

let impl_3 = impl_3'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': Core.Marker.t_Copy t_Bit

let impl_2 = impl_2'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_5': Core.Marker.t_StructuralPartialEq t_Bit

let impl_5 = impl_5'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_6': Core.Cmp.t_PartialEq t_Bit t_Bit

let impl_6 = impl_6'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_4': Core.Cmp.t_Eq t_Bit

let impl_4 = impl_4'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_7': Core.Fmt.t_Debug t_Bit

let impl_7 = impl_7'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core.Convert.t_From bool t_Bit =
  {
    f_from_pre = (fun (bit: t_Bit) -> true);
    f_from_post = (fun (bit: t_Bit) (out: bool) -> true);
    f_from
    =
    fun (bit: t_Bit) ->
      match bit <: t_Bit with
      | Bit_Zero  -> false
      | Bit_One  -> true
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8: Core.Convert.t_From u8 t_Bit =
  {
    f_from_pre = (fun (bit: t_Bit) -> true);
    f_from_post = (fun (bit: t_Bit) (out: u8) -> true);
    f_from
    =
    fun (bit: t_Bit) ->
      cast (Core.Convert.f_from #bool #t_Bit #FStar.Tactics.Typeclasses.solve bit <: bool) <: u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9: Core.Convert.t_From u16 t_Bit =
  {
    f_from_pre = (fun (bit: t_Bit) -> true);
    f_from_post = (fun (bit: t_Bit) (out: u16) -> true);
    f_from
    =
    fun (bit: t_Bit) ->
      cast (Core.Convert.f_from #bool #t_Bit #FStar.Tactics.Typeclasses.solve bit <: bool) <: u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10: Core.Convert.t_From u32 t_Bit =
  {
    f_from_pre = (fun (bit: t_Bit) -> true);
    f_from_post = (fun (bit: t_Bit) (out: u32) -> true);
    f_from
    =
    fun (bit: t_Bit) ->
      cast (Core.Convert.f_from #bool #t_Bit #FStar.Tactics.Typeclasses.solve bit <: bool) <: u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11: Core.Convert.t_From u64 t_Bit =
  {
    f_from_pre = (fun (bit: t_Bit) -> true);
    f_from_post = (fun (bit: t_Bit) (out: u64) -> true);
    f_from
    =
    fun (bit: t_Bit) ->
      cast (Core.Convert.f_from #bool #t_Bit #FStar.Tactics.Typeclasses.solve bit <: bool) <: u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_12: Core.Convert.t_From u128 t_Bit =
  {
    f_from_pre = (fun (bit: t_Bit) -> true);
    f_from_post = (fun (bit: t_Bit) (out: u128) -> true);
    f_from
    =
    fun (bit: t_Bit) ->
      cast (Core.Convert.f_from #bool #t_Bit #FStar.Tactics.Typeclasses.solve bit <: bool) <: u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_13: Core.Convert.t_From i8 t_Bit =
  {
    f_from_pre = (fun (bit: t_Bit) -> true);
    f_from_post = (fun (bit: t_Bit) (out: i8) -> true);
    f_from
    =
    fun (bit: t_Bit) ->
      cast (Core.Convert.f_from #bool #t_Bit #FStar.Tactics.Typeclasses.solve bit <: bool) <: i8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_14: Core.Convert.t_From i16 t_Bit =
  {
    f_from_pre = (fun (bit: t_Bit) -> true);
    f_from_post = (fun (bit: t_Bit) (out: i16) -> true);
    f_from
    =
    fun (bit: t_Bit) ->
      cast (Core.Convert.f_from #bool #t_Bit #FStar.Tactics.Typeclasses.solve bit <: bool) <: i16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_15: Core.Convert.t_From i32 t_Bit =
  {
    f_from_pre = (fun (bit: t_Bit) -> true);
    f_from_post = (fun (bit: t_Bit) (out: i32) -> true);
    f_from
    =
    fun (bit: t_Bit) ->
      cast (Core.Convert.f_from #bool #t_Bit #FStar.Tactics.Typeclasses.solve bit <: bool) <: i32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_16: Core.Convert.t_From i64 t_Bit =
  {
    f_from_pre = (fun (bit: t_Bit) -> true);
    f_from_post = (fun (bit: t_Bit) (out: i64) -> true);
    f_from
    =
    fun (bit: t_Bit) ->
      cast (Core.Convert.f_from #bool #t_Bit #FStar.Tactics.Typeclasses.solve bit <: bool) <: i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_17: Core.Convert.t_From i128 t_Bit =
  {
    f_from_pre = (fun (bit: t_Bit) -> true);
    f_from_post = (fun (bit: t_Bit) (out: i128) -> true);
    f_from
    =
    fun (bit: t_Bit) ->
      cast (Core.Convert.f_from #bool #t_Bit #FStar.Tactics.Typeclasses.solve bit <: bool) <: i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core.Convert.t_From t_Bit bool =
  {
    f_from_pre = (fun (b: bool) -> true);
    f_from_post = (fun (b: bool) (out: t_Bit) -> true);
    f_from
    =
    fun (b: bool) ->
      match b <: bool with
      | false -> Bit_Zero <: t_Bit
      | true -> Bit_One <: t_Bit
  }

/// A trait for types that represent machine integers.
class t_MachineInteger (v_Self: Type0) = {
  f_bits_pre:x: Prims.unit
    -> pred:
      Type0
        { (let _:Prims.unit = x in
            true) ==>
          pred };
  f_bits_post:x: Prims.unit -> bits: u32
    -> pred:
      Type0
        { pred ==>
          (let _:Prims.unit = x in
            bits >=. mk_u32 8) };
  f_bits:x0: Prims.unit -> Prims.Pure u32 (f_bits_pre x0) (fun result -> f_bits_post x0 result);
  f_SIGNED:bool
}

instance impl_MachineInteger_poly (t: inttype): t_MachineInteger (int_t t) =
  { f_bits = (fun () -> mk_u32 (bits t));
    f_bits_pre = (fun () -> True);
    f_bits_post = (fun () r -> r == mk_u32 (bits t));
    f_SIGNED = signed t }
