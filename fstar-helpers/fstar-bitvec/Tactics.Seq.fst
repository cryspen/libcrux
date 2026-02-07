module Tactics.Seq

open Core_models
module L = FStar.List.Tot
module S = FStar.Seq
open FStar.Tactics.V2
open FStar.Tactics.V2.SyntaxHelpers
open FStar.Class.Printable
open FStar.Mul
open FStar.Option

open Tactics.Utils
open Tactics.Pow2

(*** Rewrite lemmas *)
private let rw_seq_index_list #t (l: list t) i
    : Lemma (S.index (S.seq_of_list l) i == FStar.List.Tot.index l i) 
    = ()
private let rw_index_slice #typ (s: S.seq typ) i j n: Lemma (S.index (S.slice s i j) n == S.index s (normalize_term (i + n)))
  = ()
private let rw_index_upd s n v i
  : Lemma (S.index (S.upd s n v) i  == (if n = i then v else S.index s i))
  = ()

/// A version of `L.index` to mark specific instances we want to normalize.
let rec index_to_normalize #a (l: list a) (i:nat{i < L.length l}): Tot a 
  = let hd::tl = l in
    if i = 0 then hd else index_to_normalize tl (i - 1)

private let rec rw_index_to_index_to_normalize #a (l: list a) (i:nat{i < L.length l})
  : Lemma (L.index #a l i == index_to_normalize #a l i)
  = if i = 0 then () else rw_index_to_index_to_normalize (L.tl l) (i - 1)
  

(*** Tactics that apply those lemmas only if needed *)
let tactic_list_index ()
  = let?# (t, _) = expect_lhs_eq_uvar () in
    let?# (f, [typ, _; l, _; index, _]) = expect_app_n t 3 in
    let?# () = expect_free_var f (`%FStar.List.Tot.index) in
    let?# n = expect_int_literal index in
    apply_lemma_rw (`rw_index_to_index_to_normalize);
    Some ()

/// Expects `t` to be of the shape `seq_of_list #_ _`
let expect_seq_of_list (t: term): Tac (option (term & term))
  = let?# (f, [t,_; index,_]) = expect_app_n t 2 in
    let?# _ = expect_free_var f (`%S.seq_of_list) in
    Some (t, index)
    
/// Expects `t` to be of the shape `index #_ _`
let expect_seq_index (t: term): Tac (option (term & term & term))
  = let?# (f, [typ, _; l, _; index, _]) = expect_app_n t 3 in
    let?# () = expect_free_var f (`%S.index) in
    Some (typ, l, index)

/// Expects `t` to be of the shape `slice #_ _`
let expect_seq_slice (t: term): Tac (option (term & term & term & term))
  = let?# (f, [typ, _; s, _; i, _; j, _]) = expect_app_n t 4 in
    let?# () = expect_free_var f (`%S.slice) in
    Some (typ, s, i, j)
    
/// Expects `t` to be of the shape `upd #_ _`
let expect_seq_upd (t: term): Tac (option (term & term & term & term))
  = let?# (f, [typ, _; s, _; i, _; v, _]) = expect_app_n t 4 in
    let?# () = expect_free_var f (`%S.upd) in
    Some (typ, s, i, v)

let tactic_seq_index_of_list ()
  = let?# (t, _) = expect_lhs_eq_uvar () in
    let?# (_, l, _) = expect_seq_index t in
    let?# _ = expect_seq_of_list l in
    apply_lemma_rw (`rw_seq_index_list);
    Some ()

let tactic_rw_index_slice ()
  = let?# (t, _) = expect_lhs_eq_uvar () in
    let?# (typ, s, index) = expect_seq_index t in
    let?# (_, s, i, j) = expect_seq_slice s in
    apply_lemma_rw (`rw_index_slice #(`#typ) (`#s) (`#i) (`#j));
    Some ()

let tactic_rw_index_upd ()
  = let?# (t, _) = expect_lhs_eq_uvar () in
    let?# (typ, s, index) = expect_seq_index t in
    let?# (_, s, i, v) = expect_seq_upd s in
    apply_lemma_rw (`rw_index_upd #(`#typ) (`#s) (`#i) (`#v));
    Some ()

(*** Final tactics *)
let norm_zeta_full_list_index (): Tac unit
  = norm [iota; primops; zeta_full; delta_only [`%index_to_normalize]]


let norm_index_minimal (): Tac unit
  = pointwise ((unwrap ∘ tactic_list_index) ||> trefl);
    norm_zeta_full_list_index ()

let norm_index' (): Tac unit
  = pointwise (   (unwrap ∘ tactic_seq_index_of_list)
              ||> (unwrap ∘ tactic_list_index)
              ||> (unwrap ∘ tactic_rw_index_slice)
              ||> (unwrap ∘ tactic_rw_index_upd)
              ||> trefl)

let norm_index (): Tac unit
  = goal_fixpoint norm_index' ();
    norm_zeta_full_list_index ()


(*** Tests *)
let _ = assert (
    let s = S.seq_of_list [1;2;3;4;5;6] in
    let s = S.slice s 2 4 in
    S.index s 1 == 4
) by (norm []; norm_index (); trefl ())

let _ = assert (
  L.index [L.index [1;2;3;4;5;6] (L.index [1;2;3;4;3;3] 2)] 0 == 4
) by (norm_index(); trefl ())
let _ = assert (
  S.index (S.seq_of_list [1;2;3;(S.index (S.seq_of_list [1;2;3;(S.index (S.seq_of_list [1;2;3;4;1]) 3);1]) 3);1]) 3 == 4
) by (norm_index(); trefl ())

