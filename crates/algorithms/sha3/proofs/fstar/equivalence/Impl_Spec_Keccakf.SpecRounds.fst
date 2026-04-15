module Impl_Spec_Keccakf.SpecRounds

(** Spec-side recursive round iteration and the [keccak_f == spec_rounds]
    bridge.

    [Hacspec_sha3.Keccak_f.keccak_f] is defined as a [fold_range 0 24]
    over a spec-only one-round body (theta∘rho∘pi∘chi∘iota). We re-express
    the same iteration recursively as [spec_rounds], and prove the two
    are equal in a single SMT query.

    The bridge [lemma_keccak_f_is_rounds] uses [--fuel 25] to unfold
    both the [fold_range] (24 steps) and [spec_rounds] (24 steps). This
    setting is fragile to perturbations in the surrounding SMT context,
    so the lemma is isolated in this small module — its only dependency
    is [Hacspec_sha3.Keccak_f]. The consumer (Generic.fst) imports this
    module qualified as [SpecRounds]. *)

#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"

open FStar.Mul
open Core_models
open Rust_primitives.Integers

let spec_state = t_Array u64 (mk_usize 25)

let spec_one_round (state: spec_state) (i: usize)
  : Pure spec_state (requires i <. mk_usize 24) (fun _ -> True) =
  Hacspec_sha3.Keccak_f.iota
    (Hacspec_sha3.Keccak_f.chi
      (Hacspec_sha3.Keccak_f.pi
        (Hacspec_sha3.Keccak_f.rho
          (Hacspec_sha3.Keccak_f.theta state))))
    i

let rec spec_rounds (state: spec_state) (r: usize)
  : Pure spec_state
      (requires r <=. mk_usize 24) (fun _ -> True)
      (decreases (v (mk_usize 24) - v r)) =
  if r =. mk_usize 24 then state
  else spec_rounds (spec_one_round state r) (r +! mk_usize 1)

(** Bridge: spec's [keccak_f] equals [spec_rounds].

    The spec body is simple — no refined argument types, no extractor
    identity let-bindings beyond the outer [let state = fold_range ... in
    state] wrapper — so Z3 can unroll all 24 iterations of the
    [fold_range] directly once it also unfolds [spec_rounds]. [fuel 25]
    is enough for both unfoldings.

    Kept in its own module so the high fuel does not perturb the
    surrounding SMT context in [Impl_Spec_Keccakf.Generic]. *)

#push-options "--fuel 25 --ifuel 1 --z3rlimit 600"
let lemma_keccak_f_is_rounds (state: spec_state)
  : Lemma (Hacspec_sha3.Keccak_f.keccak_f state ==
           spec_rounds state (mk_usize 0))
  = ()
#pop-options
