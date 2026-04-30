module Hacspec_ml_kem.Parameters.Sizes
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

(* Parameterized (rank-indexed) size constants for ML-KEM, mirroring
   the Spec.MLKEM versions but in the Hacspec_ml_kem namespace.  Lets
   `src/ind_cpa.rs` and `src/ind_cca.rs` ensures cite the canonical
   spec without pulling Spec.MLKEM into scope.

   Uses the underlying file-scope constants from `Hacspec_ml_kem.Parameters`
   (`v_BYTES_PER_RING_ELEMENT`, etc.).  `is_rank`/`rank` are duplicated
   here intentionally — Spec.MLKEM is being deleted, so callers should
   not need to depend on Spec.MLKEM.Math for the rank refinement.

   Equality lemmas (`lemma_*_eq`) at the bottom let consumers transition
   incrementally: cite the `Hacspec_ml_kem.Parameters.Sizes.*` form,
   then invoke the lemma to discharge an old `Spec.MLKEM.*`-shaped
   obligation. *)

module P = Hacspec_ml_kem.Parameters

let is_rank (r:usize) : Type0 = r == sz 2 \/ r == sz 3 \/ r == sz 4

type rank = r:usize{is_rank r}

(*** Top-5 Spec.MLKEM constants, rank-parameterized ***)

val v_ETA1 (r:rank) : u:usize{u == sz 3 \/ u == sz 2}
let v_ETA1 (r:rank) : usize =
  if r = sz 2 then sz 3 else sz 2

val v_ETA1_RANDOMNESS_SIZE (r:rank) : u:usize{u == sz 128 \/ u == sz 192}
let v_ETA1_RANDOMNESS_SIZE (r:rank) : usize = v_ETA1 r *! sz 64

val v_RANKED_BYTES_PER_RING_ELEMENT (r:rank) : u:usize{u = sz 768 \/ u = sz 1152 \/ u = sz 1536}
let v_RANKED_BYTES_PER_RING_ELEMENT (r:rank) : usize = r *! P.v_BYTES_PER_RING_ELEMENT

val v_CPA_PUBLIC_KEY_SIZE (r:rank) : u:usize{u = sz 800 \/ u = sz 1184 \/ u = sz 1568}
let v_CPA_PUBLIC_KEY_SIZE (r:rank) : usize =
  v_RANKED_BYTES_PER_RING_ELEMENT r +! sz 32

let v_CPA_PRIVATE_KEY_SIZE (r:rank) : usize = v_RANKED_BYTES_PER_RING_ELEMENT r

val v_CCA_PRIVATE_KEY_SIZE (r:rank) : u:usize{u = sz 1632 \/ u = sz 2400 \/ u = sz 3168}
let v_CCA_PRIVATE_KEY_SIZE (r:rank) : usize =
  v_CPA_PRIVATE_KEY_SIZE r +! v_CPA_PUBLIC_KEY_SIZE r +! sz 32 +! sz 32

(*** Equality bridges to Spec.MLKEM (transitional — to be deleted with Spec.MLKEM) ***)

let lemma_v_ETA1_eq (r:rank) : Lemma
  (v_ETA1 r == Spec.MLKEM.v_ETA1 r) = ()

let lemma_v_ETA1_RANDOMNESS_SIZE_eq (r:rank) : Lemma
  (v_ETA1_RANDOMNESS_SIZE r == Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE r)
  = lemma_v_ETA1_eq r

let lemma_v_RANKED_BYTES_PER_RING_ELEMENT_eq (r:rank) : Lemma
  (v_RANKED_BYTES_PER_RING_ELEMENT r == Spec.MLKEM.v_RANKED_BYTES_PER_RING_ELEMENT r) = ()

let lemma_v_CPA_PUBLIC_KEY_SIZE_eq (r:rank) : Lemma
  (v_CPA_PUBLIC_KEY_SIZE r == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE r)
  = lemma_v_RANKED_BYTES_PER_RING_ELEMENT_eq r

let lemma_v_CCA_PRIVATE_KEY_SIZE_eq (r:rank) : Lemma
  (v_CCA_PRIVATE_KEY_SIZE r == Spec.MLKEM.v_CCA_PRIVATE_KEY_SIZE r)
  = lemma_v_CPA_PUBLIC_KEY_SIZE_eq r;
    lemma_v_RANKED_BYTES_PER_RING_ELEMENT_eq r
