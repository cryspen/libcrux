module Tactics.Folds

open Core_models
module L = FStar.List.Tot
module S = FStar.Seq.Base
open FStar.Tactics.V2
open FStar.Tactics.V2.SyntaxHelpers
open FStar.Class.Printable
open FStar.Mul
open FStar.Option

open Rust_primitives.Hax.Folds

open Tactics.Utils

// let unfold_fold_range
//   (#acc_t: Type0) (#u: Lib.IntTypes.inttype)
//   (start_: int_t u)
//   (end_: int_t u)
//   (inv: acc_t -> (i:int_t u{fold_range_wf_index start_ end_ false (v i)}) -> Type0)
//   (init: acc_t {inv init start_})
//   (f: (acc:acc_t -> i:int_t u  {v i <= v end_ /\ fold_range_wf_index start_ end_ true (v i) /\ inv acc i}
//                  -> acc':acc_t {(inv acc' (mk_int (v i + 1)))}))
//    = if v start_ < v end_
//      then fold_range (start_ +! mk_int 1) end_ inv (f init start_) f
//      else init


// #push-options "--z3rlimit 100"
// let unfold_fold_range
//   (#acc_t: Type0) (#u: Lib.IntTypes.inttype)
//   (start_: int_t u)
//   (end_: int_t u)
//   (inv: acc_t -> (i:int_t u{fold_range_wf_index start_ end_ false (v i)}) -> Type0)
//   (init: acc_t {inv init start_})
//   (f: (acc:acc_t -> i:int_t u  {v i <= v end_ /\ fold_range_wf_index start_ end_ true (v i) /\ inv acc i}
//                  -> acc':acc_t {(inv acc' (mk_int (v i + 1)))}))
//   : Lemma (  fold_range start_ end_ inv init f 
//           == ( if v start_ < v end_
//                then 
//                  fold_range (start_ +! mk_int 1) end_ inv (f init start_) f
//                else init )
//     )
//   = admit ()
// #pop-options

// let expect_fold_range t
//   = let?# (fr, [acc_t,_;u,_;start_,_;end_,_;inv,_;init,_;f,_]) = expect_app_n t 7 in
//     let _ = expect_free_var fr (`%fold_range) in
//     Some (acc_t, u, start_, end_, inv, init, f)

// let make_fold_range_lemma (start_: nat) (end_: nat): Tac _ = 
//   let _ = tcut (quote (squash (forall acc_t u inv init f. 
//        fold_range #acc_t #u start_ end_ inv init f
//     == fold_range #acc_t #u start_ end_ inv init f
//   ))) in
//   flip ();
//   let acc_t = forall_intro () in
//   let u = forall_intro () in
//   let inv = forall_intro () in
//   let init = forall_intro () in
//   let f = forall_intro () in
//   fail "xx";
//   let _ = rewrite_rhs () in
//   flip ();
//   focus (fun _ ->
//     fail "xx";
//     apply_lemma_rw (`unfold_fold_range)
//   );
//   ()
//   // rewrite_lhs
// //   let aux start_ =

// jlet _ = 
//   assert true by (make_fold_range_lemma 1 10)

//   in
  

// let tactic_fold_range t
//   = let?# expect_fold_range _ = 

