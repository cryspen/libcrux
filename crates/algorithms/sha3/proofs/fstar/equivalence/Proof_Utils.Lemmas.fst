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
