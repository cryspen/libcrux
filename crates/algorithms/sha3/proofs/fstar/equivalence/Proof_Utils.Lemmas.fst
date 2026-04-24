module Proof_Utils.Lemmas

(** Library-level lemmas that belong in hax-lib / core-models but are not
    currently exposed by those interfaces. Each lemma below is true for
    concrete machine integers but is not provable from the abstract F*
    interface in [Rust_primitives.Integers] / [Core_models.Num]. They
    are kept here as [admit ()]s with [TODO] tags so that downstream
    users can call them from a single well-known location, and so that
    the eventual upstream fix replaces only this file.

    Upstream targets:
      - [logand_commutative]        — [Rust_primitives.Integers] (hax-lib)
      - [lemma_rotate_left_zero]    — [Core_models.Num] / hax-lib *)

#set-options "--fuel 0 --ifuel 1 --z3rlimit 50"

open FStar.Mul
open Core_models
open Rust_primitives.Integers

(** Bitwise AND commutativity. True for machine integers but not
    provable from the abstract [logand] interface in
    [Rust_primitives.Integers]. Belongs in hax-lib. *)
let logand_commutative (#t: inttype) (a b: int_t t)
  : Lemma ((a &. b) == (b &. a))
  = admit ()

(** [rotate_left(x, 0) == x]. True by definition but [rotate_left] is
    opaque in the core-models abstraction. Belongs in
    [Core_models.Num] / hax-lib. *)
let lemma_rotate_left_zero (x: u64)
  : Lemma (Core_models.Num.impl_u64__rotate_left x (mk_u32 0) == x)
  = admit ()

(* Update at Range Indexing Property *)
(* This is a more useful spec than the one in Monomorphized_update_at *)
let lemma_index_update_at_range #t (s:t_Slice t) (i:Core_models.Ops.Range.t_Range usize) (x:t_Slice t):
  Lemma 
  (requires 
    v i.f_start >= 0 /\ v i.f_start <= Seq.length s /\
    v i.f_end <= Seq.length s /\
    Seq.length x == v i.f_end - v i.f_start)
  (ensures (
  let open Core_models.Ops.Range in
  let out = Rust_primitives.Hax.Monomorphized_update_at.update_at_range s i x in
  Seq.length out == Seq.length s /\
 (forall (j:nat). if j < v i.f_start then 
    Seq.index out j == Seq.index s j 
  else if j >= v i.f_start && j < v i.f_end then 
    Seq.index out j == Seq.index x (j - v i.f_start)
  else if j >= v i.f_end && j < Seq.length out then 
    Seq.index out j == Seq.index s j
  else True))) =
  admit ()
