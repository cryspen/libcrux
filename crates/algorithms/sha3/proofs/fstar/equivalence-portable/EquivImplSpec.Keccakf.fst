module EquivImplSpec.Keccakf

(* ================================================================
   Thin shim forwarding the Keccak-f[1600] equivalence theorem to
   [EquivImplSpec.Keccakf.Portable].

   Historically this module contained a bespoke portable-only proof
   of [keccakf1600 ≡ keccak_f]. After the SHA-3 state-layout flip to
   FIPS-native [state[5*y + x]], that proof required invasive
   re-engineering; meanwhile [EquivImplSpec.Keccakf.Generic] +
   [EquivImplSpec.Keccakf.Portable] already establish the same theorem
   via the generic lane-wise path. To avoid duplicated maintenance,
   the concrete portable proof has been replaced with a one-liner
   call into [Portable.lemma_keccakf1600_portable].

   Public surface kept stable for [EquivImplSpec.Sponge.*] consumers:
     - [impl_state], [spec_state]    — shorthands
     - [lemma_fold_range_step]       — re-exported from
                                       [Proof_Utils.FoldRange]
     - [lemma_set_ij_unfold]         — [set_ij] layout lemma
     - [lemma_keccakf1600_equiv]     — main theorem
   ================================================================ *)

#set-options "--fuel 0 --ifuel 1 --z3rlimit 50"

open FStar.Mul
open Core_models
open Rust_primitives.Integers

module P = EquivImplSpec.Keccakf.Portable
module FR = Proof_Utils.FoldRange

(* Bring typeclass instances into scope so that
   t_KeccakItem u64 (mk_usize 1) resolves to the portable impl. *)
let _ =
  let open Libcrux_sha3.Traits in
  let open Libcrux_sha3.Simd.Portable in
  ()

(** Shorthand for the impl's state type. *)
let impl_state = Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64

(** Shorthand for the spec's state type. *)
let spec_state = t_Array u64 (mk_usize 25)

(** Re-export of [Proof_Utils.FoldRange.lemma_fold_range_step] so
    consumers that still say [EquivImplSpec.Keccakf.lemma_fold_range_step]
    keep compiling without churn. *)
let lemma_fold_range_step
      (#acc_t: Type0)
      (start end_: usize)
      (inv: acc_t -> (i:usize{Rust_primitives.Hax.Folds.fold_range_wf_index start end_ false (v i)}) -> Type0)
      (init: acc_t {~(Rust_primitives.Hax.Folds.range_empty start end_) ==> inv init start})
      (f: (acc:acc_t -> i:usize {v i <= v end_ /\ Rust_primitives.Hax.Folds.fold_range_wf_index start end_ true (v i) /\ inv acc i}
                     -> acc':acc_t {(inv acc' (mk_int (v i + 1)))}))
  : Lemma
      (requires v start < v end_)
      (ensures Rust_primitives.Hax.Folds.fold_range start end_ inv init f ==
               Rust_primitives.Hax.Folds.fold_range (start +! mk_usize 1) end_ inv (f init start) f)
  = FR.lemma_fold_range_step start end_ inv init f

(** The impl's [set_ij] unfolds to [update_at_usize] at index [5*i + j].
    Under the FIPS-native layout, [get_ij(arr, i, j) = arr[5*i + j]] where
    the impl's [(i, j)] corresponds to FIPS [(y, x)]; concretely
    [5*i + j] is the flat index of lane [A[j, i]] in the spec's convention. *)
let lemma_set_ij_unfold (s: spec_state) (i j: usize) (v: u64)
  : Lemma (requires i <. mk_usize 5 /\ j <. mk_usize 5)
          (ensures  Libcrux_sha3.Traits.set_ij (mk_usize 1) s i j v ==
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
                      ((mk_usize 5 *! i <: usize) +! j) v)
  = ()

(** MAIN THEOREM: the impl's [keccakf1600] at N=1 equals the spec's
    [keccak_f] pointwise on the underlying state. Discharged by
    [EquivImplSpec.Keccakf.Portable.lemma_keccakf1600_portable]. *)
let lemma_keccakf1600_equiv
      (ks: impl_state)
      (state: spec_state)
  : Lemma
      (requires ks.Libcrux_sha3.Generic_keccak.f_st == state)
      (ensures
        (Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 (mk_usize 1) #u64 ks)
          .Libcrux_sha3.Generic_keccak.f_st ==
        Hacspec_sha3.Keccak_f.keccak_f state)
  = P.lemma_keccakf1600_portable ks
