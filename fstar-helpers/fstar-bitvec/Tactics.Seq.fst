module Tactics.Seq

open Core
module L = FStar.List.Tot
open FStar.Tactics.V2
open FStar.Tactics.V2.SyntaxHelpers
open FStar.Class.Printable
open FStar.Mul
open FStar.Option

open Tactics.Utils
open Tactics.Pow2

let rw_seq_index_list #t (l: list t) i
    : Lemma (Seq.Base.index (Seq.Base.seq_of_list l) i == FStar.List.Tot.index l i) 
    = ()

private let unfold_index_lemma (#a: Type) (l: list a) (i:nat{i < List.Tot.length l})
  : Lemma (  FStar.List.Tot.index #a l i 
          == Pervasives.norm [iota; primops] (let hd::tl = l in
    if i = 0 then hd else List.Tot.index tl (i - 1)))
  = ()

private exception DoRefl
private exception StopNormIndex
let norm_list_index (): Tac unit =
  let _ = repeat (fun _ ->
    lset "found" false;
    pointwise (fun _ ->
      (fun () ->
         match let?# (t, _) = expect_lhs_eq_uvar () in
               let?# (f, [typ, _; l, _; index, _]) = expect_app_n t 3 in
               let?# () = expect_free_var f (`%FStar.List.Tot.index) in
               let?# n = expect_int_literal index in
               apply_lemma_rw (`unfold_index_lemma);
               lset "found" true;
               Some ()
         with | Some () -> () | _ -> raise DoRefl
      ) `or_else` trefl);
    if lget "found" then () else raise StopNormIndex) in ()

let _ = assert (L.index [1;2;3;4;5;6] 3 == 4) by (norm_list_index(); trefl ())

let simplify_index_seq_of_list () = l_to_r [`rw_seq_index_list]

let norm_index (): Tac unit
  = norm_list_index ();
    simplify_index_seq_of_list ()

