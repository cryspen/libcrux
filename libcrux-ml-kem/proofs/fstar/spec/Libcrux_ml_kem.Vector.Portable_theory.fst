module Libcrux_ml_kem.Vector.Portable_theory
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

(* Companion lemmas factored out of `src/vector/portable.rs` body proof
   blocks (Plan C): each lemma packages one function's inline proof script
   as a named, independently verified statement over plain i16 arrays, so
   the Rust body carries a one-line `proof!` call instead of the script.
   Everything here is over `t_Array i16` + scalars — no typeclass instances,
   no references back into `Libcrux_ml_kem.Vector.Portable` (module-cycle
   free). *)

module TS = Libcrux_ml_kem.Vector.Traits.Spec
module CC = Hacspec_ml_kem.Commute.Chunk

(* op_ntt_layer_2_step, closing block: from the butterfly post of
   `ntt_layer_2_step` derive the four per-branch spec-commute facts the
   function's `ntt_layer_2_step_post` requires.  One top-level lemma per
   branch (a shared-context 4-way dispatch saturates on one branch — the
   per-lane/top-level shape verifies each in ms), then a trivial combiner. *)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 300 --split_queries always"
#restart-solver
let lemma_ntt_layer_2_branch
    (a out: t_Array i16 (mk_usize 16))
    (zeta0 zeta1: i16)
    (b: nat{b < 4})
  : Lemma
    (requires Spec.Utils.ntt_layer_2_butterfly_post a out zeta0 zeta1)
    (ensures TS.ntt_layer_2_step_branch_post b a zeta0 zeta1 out)
  = reveal_opaque (`%Spec.Utils.ntt_layer_2_butterfly_post)
                  (Spec.Utils.ntt_layer_2_butterfly_post a);
    reveal_opaque (`%TS.ntt_layer_2_step_branch_post)
                  TS.ntt_layer_2_step_branch_post;
    let z = if b < 2 then zeta0 else zeta1 in
    let base : nat = if b < 2 then 0 else 8 in
    let off  : nat = if b = 0 || b = 2 then 0 else 2 in
    let i1 : nat = base + off in
    CC.lemma_butterfly_pair_commute a out z i1 (i1 + 4);
    CC.lemma_butterfly_pair_commute a out z (i1 + 1) (i1 + 5)
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 100 --split_queries always"
#restart-solver
let lemma_ntt_layer_2_step_commute
    (a out: t_Array i16 (mk_usize 16))
    (zeta0 zeta1: i16)
  : Lemma
    (requires Spec.Utils.ntt_layer_2_butterfly_post a out zeta0 zeta1)
    (ensures
      Spec.Utils.forall4 (fun (b: nat{b < 4}) ->
        TS.ntt_layer_2_step_branch_post b a zeta0 zeta1 out))
  = lemma_ntt_layer_2_branch a out zeta0 zeta1 0;
    lemma_ntt_layer_2_branch a out zeta0 zeta1 1;
    lemma_ntt_layer_2_branch a out zeta0 zeta1 2;
    lemma_ntt_layer_2_branch a out zeta0 zeta1 3
#pop-options
