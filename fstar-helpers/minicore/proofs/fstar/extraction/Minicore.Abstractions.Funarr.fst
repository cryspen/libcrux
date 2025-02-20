module Minicore.Abstractions.Funarr
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

open FStar.FunctionalExtensionality
type t_FunArray (n: usize) (t: Type0) = i:usize {v i < v n} ^-> t

let impl_6__get (v_N: usize) (#v_T: Type0) (self: t_FunArray v_N v_T) (i: usize {v i < v v_N}) : v_T = 
    self i

let impl_6__from_fn
    (v_N: usize)
    (#v_T: Type0)
    (f: (i: usize {v i < v v_N}) -> v_T)
    : t_FunArray v_N v_T = on (i: usize {v i < v v_N}) f

let impl_6__as_slice n #t (self: t_FunArray n t) = FStar.Seq.init (v n) (fun i -> self (mk_usize i))

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': v_N: usize -> #v_T: Type0 -> {| i1: Core.Clone.t_Clone v_T |}
  -> Core.Clone.t_Clone (t_FunArray v_N v_T)

let impl_2
      (v_N: usize)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
     = impl_2' v_N #v_T #i1

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': v_N: usize -> #v_T: Type0 -> {| i1: Core.Marker.t_Copy v_T |}
  -> Core.Marker.t_Copy (t_FunArray v_N v_T)

let impl_1
      (v_N: usize)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Marker.t_Copy v_T)
     = impl_1' v_N #v_T #i1

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_4': v_N: usize -> #v_T: Type0 -> Core.Marker.t_StructuralPartialEq (t_FunArray v_N v_T)

let impl_4 (v_N: usize) (#v_T: Type0) = impl_4' v_N #v_T

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_5': v_N: usize -> #v_T: Type0 -> {| i1: Core.Cmp.t_PartialEq v_T v_T |}
  -> Core.Cmp.t_PartialEq (t_FunArray v_N v_T) (t_FunArray v_N v_T)

let impl_5
      (v_N: usize)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Cmp.t_PartialEq v_T v_T)
     = impl_5' v_N #v_T #i1

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': v_N: usize -> #v_T: Type0 -> {| i1: Core.Cmp.t_Eq v_T |}
  -> Core.Cmp.t_Eq (t_FunArray v_N v_T)

let impl_3
      (v_N: usize)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Cmp.t_Eq v_T)
     = impl_3' v_N #v_T #i1

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7 (v_N: usize) (#v_T: Type0) : Core.Ops.Index.t_Index (t_FunArray v_N v_T) usize =
  {
    f_Output = v_T;
    f_index_pre = (fun (self_: t_FunArray v_N v_T) (index: usize) -> index <. v_N);
    f_index_post = (fun (self: t_FunArray v_N v_T) (index: usize) (out: v_T) -> true);
    f_index = fun (self: t_FunArray v_N v_T) (index: usize) -> impl_6__get v_N #v_T self index
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (v_N: usize) (#v_T: Type0) : Core.Convert.t_AsRef (t_FunArray v_N v_T) (t_Slice v_T) =
  {
    f_as_ref_pre = (fun (self: t_FunArray v_N v_T) -> true);
    f_as_ref_post = (fun (self: t_FunArray v_N v_T) (out: t_Slice v_T) -> true);
    f_as_ref = fun (self: t_FunArray v_N v_T) -> impl_6__as_slice v_N #v_T self
  }
