module Minicore.Abstractions.Funarr
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

open FStar.Tactics

let e_pointwise_apply_mk_term #t
  (max: nat)
  (f: (n:nat {n < max}) -> t)
  : Tac unit
  = let rec brs (n:int): Tac _ =
      if n < 0 then []
      else
        let c = C_Int n in
        let p = Pat_Constant c in
        (p, mk_e_app (quote f) [pack (Tv_Const c)])::brs (n - 1)
    in
    let bd = fresh_binder_named "i" (quote (m: nat {m < max})) in
    let t = mk_abs [bd] (Tv_Match bd None (brs (max - 1))) in
    exact t

open FStar.FunctionalExtensionality    
type t_FunArray (n: u64) (t: Type0) = i:u64 {v i < v n} ^-> t

let pointwise_apply 
    (v_N: u64) (#v_T: Type0) (f: t_FunArray v_N v_T)
    (#[e_pointwise_apply_mk_term (v v_N) (fun (i:nat{i < v v_N}) -> f (mk_u64 i))] def: (n: nat {n < v v_N}) -> v_T)
    : t_FunArray v_N v_T
    = on (i: u64 {v i < v v_N}) (fun i -> def (v i))

let impl_5__get (v_N: u64) (#v_T: Type0) (self: t_FunArray v_N v_T) (i: u64 {v i < v v_N}) : v_T = 
    self i

let impl_5__from_fn
    (v_N: u64)
    (#v_T: Type0)
    (f: (i: u64 {v i < v v_N}) -> v_T)
    : t_FunArray v_N v_T = on (i: u64 {v i < v v_N}) f

let impl_5__as_vec n #t (self: t_FunArray n t) = FStar.Seq.init (v n) (fun i -> self (mk_u64 i))

let rec impl_5__fold n #t #a (arr: t_FunArray n t) (init: a) (f: a -> t -> a): Tot a (decreases (v n)) = 
    match n with
    | MkInt 0 -> init
    | MkInt n -> 
        let acc: a = f init (arr (mk_u64 0)) in 
        let n = MkInt (n - 1) in
        impl_5__fold  n #t #a
                      (impl_5__from_fn n (fun i -> arr (i +. mk_u64 1)))
                      acc f

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': v_N: u64 -> #v_T: Type0 -> {| i1: Core.Clone.t_Clone v_T |}
  -> Core.Clone.t_Clone (t_FunArray v_N v_T)

let impl_1
      (v_N: u64)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
     = impl_1' v_N #v_T #i1

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl': v_N: u64 -> #v_T: Type0 -> {| i1: Core.Marker.t_Copy v_T |}
  -> Core.Marker.t_Copy (t_FunArray v_N v_T)

let impl
      (v_N: u64)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Marker.t_Copy v_T)
     = impl' v_N #v_T #i1

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': v_N: u64 -> #v_T: Type0 -> Core.Marker.t_StructuralPartialEq (t_FunArray v_N v_T)

let impl_3 (v_N: u64) (#v_T: Type0) = impl_3' v_N #v_T

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_4': v_N: u64 -> #v_T: Type0 -> {| i1: Core.Cmp.t_PartialEq v_T v_T |}
  -> Core.Cmp.t_PartialEq (t_FunArray v_N v_T) (t_FunArray v_N v_T)

let impl_4
      (v_N: u64)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Cmp.t_PartialEq v_T v_T)
     = impl_4' v_N #v_T #i1

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': v_N: u64 -> #v_T: Type0 -> {| i1: Core.Cmp.t_Eq v_T |}
  -> Core.Cmp.t_Eq (t_FunArray v_N v_T)

let impl_2
      (v_N: u64)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Cmp.t_Eq v_T)
     = impl_2' v_N #v_T #i1

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8 (v_N: u64) (#v_T: Type0) : Core.Ops.Index.t_Index (t_FunArray v_N v_T) u64 =
  {
    f_Output = v_T;
    f_index_pre = (fun (self_: t_FunArray v_N v_T) (index: u64) -> index <. v_N);
    f_index_post = (fun (self: t_FunArray v_N v_T) (index: u64) (out: v_T) -> true);
    f_index = fun (self: t_FunArray v_N v_T) (index: u64) -> impl_5__get v_N #v_T self index
  }
