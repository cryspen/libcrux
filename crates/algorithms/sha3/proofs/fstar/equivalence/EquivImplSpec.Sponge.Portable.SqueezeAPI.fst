module EquivImplSpec.Sponge.Portable.SqueezeAPI

(* ================================================================
   Portable squeeze driver equivalence.

   Proves: Libcrux_sha3.Generic_keccak.Portable.squeeze ≡
           Hacspec_sha3.Sponge.squeeze

   Structure: mirrors [lemma_absorb_portable_aux].  The spec-side
   [Hacspec_sha3.Sponge.squeeze] delegates its middle loop to a
   recursive helper [Hacspec_sha3.Sponge.squeeze_blocks]; the
   equivalence pairs the impl's [fold_range 1 output_blocks]
   iteration-for-iteration against that recursion via
   [Proof_Utils.FoldRange.lemma_fold_range_step].
   ================================================================ *)

#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"

open FStar.Mul
open Core_models

module SP = EquivImplSpec.Sponge.Portable
module KP = EquivImplSpec.Keccakf.Portable
module Steps = EquivImplSpec.Sponge.Portable.Steps
module HS = Hacspec_sha3.Sponge

(* Bring Portable typeclass instances into scope. *)
let _ =
  let open Libcrux_sha3.Traits in
  let open Libcrux_sha3.Simd.Portable in
  ()


(* ================================================================
   Step 1: f_squeeze (no keccakf) ≡ squeeze_state.
   ================================================================ *)
#push-options "--z3rlimit 100"
let lemma_squeeze_once_portable
      (rate: usize)
      (ks: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
      (out: t_Slice u8)
      (start: usize)
      (len: usize)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v len <= v rate /\
        v start + v len <= Seq.length #u8 out)
      (ensures (
        let out' = Libcrux_sha3.Traits.f_squeeze
                     #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
                     #u64
                     #FStar.Tactics.Typeclasses.solve
                     rate ks out start len in
        out' == HS.squeeze_state
                  (Core_models.Slice.impl__len #u8 out)
                  ks.Libcrux_sha3.Generic_keccak.f_st
                  (out <: t_Array u8 _) start len))
  = let outputs : t_Array (t_Slice u8) (mk_usize 1) =
      let list = [out] in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
      Rust_primitives.Hax.array_of_list 1 list in
    assert (outputs.[ mk_usize 0 ] == out);
    SP.portable_sc_store_block rate ks.Libcrux_sha3.Generic_keccak.f_st
      outputs start len 0;
    KP.lemma_extract_lane_portable_identity ks.Libcrux_sha3.Generic_keccak.f_st
#pop-options


(* NOTE: the former middle-loop lockstep induction [lemma_squeeze_portable_aux]
   and the re-exports of [lemma_squeeze_blocks_unfold]/[lemma_squeeze_blocks_tail]
   have been removed.

   The lockstep induction has been pushed into the Rust-side [squeeze]'s ensures
   clause (see [Libcrux_sha3.Generic_keccak.Portable.squeeze]): its postcondition
   now asserts equality with [EquivImplSpec.Sponge.Portable.Steps.portable_squeeze_composed]
   directly, with the fold-range → [squeeze_blocks] bridge discharged inline by
   [Hacspec_sha3.Sponge.Lemmas.lemma_squeeze_blocks_tail] and
   [Steps.lemma_squeeze_block_portable]. The remaining work — reconciling
   [portable_squeeze_composed] with [Hacspec_sha3.Sponge.squeeze] itself —
   is done by [EquivImplSpec.Sponge.Portable.API.lemma_squeeze_portable]. *)
