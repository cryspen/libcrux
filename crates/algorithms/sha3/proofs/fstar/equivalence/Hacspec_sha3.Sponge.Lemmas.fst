module Hacspec_sha3.Sponge.Lemmas

(* ================================================================
   Spec-side lemmas about [Hacspec_sha3.Sponge.squeeze_blocks].

   Kept in a standalone module with no [Libcrux_sha3.*] dependency
   so that both the equivalence proofs (in [EquivImplSpec.*]) and
   the extracted Rust code (via [hax_lib::fstar!] ghost blocks in
   [Libcrux_sha3.Generic_keccak.Portable]) can reference them
   without introducing a dependency cycle.
   ================================================================ *)

#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"

open FStar.Mul
open Core_models
open Rust_primitives.Integers

module HS = Hacspec_sha3.Sponge


(* ================================================================
   Base case of [squeeze_blocks]: when [i == j], the recursion
   returns the input [(state, output)] unchanged.  Stated as a
   lemma with fuel 1 so callers at fuel 0 can rely on it.
   ================================================================ *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"
let lemma_squeeze_blocks_base
      (output_len: usize)
      (state: t_Array u64 (mk_usize 25))
      (rate i: usize)
      (output: t_Array u8 output_len)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v i <= v output_len / v rate)
      (ensures HS.squeeze_blocks output_len state rate i i output == (state, output))
  = ()
#pop-options


(* ================================================================
   Head-unfold of [squeeze_blocks]: unfold one iteration from the
   left (at index [i]).
   ================================================================ *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 100 --split_queries always"
let lemma_squeeze_blocks_unfold
      (output_len: usize)
      (state: t_Array u64 (mk_usize 25))
      (rate i output_blocks: usize)
      (output: t_Array u8 output_len)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v i < v output_blocks /\
        v output_blocks * v rate <= v output_len)
      (ensures (
        let state' = Hacspec_sha3.Keccak_f.keccak_f state in
        let output' = HS.squeeze_state output_len state' output (i *! rate) rate in
        HS.squeeze_blocks output_len state rate i output_blocks output ==
        HS.squeeze_blocks output_len state' rate (i +! mk_usize 1) output_blocks output'))
  = FStar.Math.Lemmas.lemma_div_le
      (v output_blocks * v rate) (v output_len) (v rate);
    FStar.Math.Lemmas.cancel_mul_div (v output_blocks) (v rate)
#pop-options



(* ================================================================
   Tail-unfold of [squeeze_blocks]: extend the recursion by one
   step on the right (at index [output_blocks]) rather than the
   usual left-unfold at [i].

   Dual to [lemma_squeeze_blocks_unfold].  Needed to reason about
   the Rust impl's [fold_range 1 output_blocks] loop body, which
   extends work done through iteration [i-1] with one more step
   at [i] — i.e. right-extension, not head-unfolding.

   Proved by induction on [output_blocks - i], chaining the existing
   head-unfold lemma.
   ================================================================ *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 300"
let rec lemma_squeeze_blocks_tail
      (output_len: usize)
      (state: t_Array u64 (mk_usize 25))
      (rate i j k: usize)
      (output: t_Array u8 output_len)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v i <= v j /\
        v k == v j + 1 /\
        v k <= v output_len / v rate)
      (ensures (
        let (state_mid, out_mid) =
          HS.squeeze_blocks output_len state rate i j output in
        let state_next = Hacspec_sha3.Keccak_f.keccak_f state_mid in
        let out_next =
          HS.squeeze_state output_len state_next out_mid (j *! rate) rate in
        HS.squeeze_blocks output_len state rate i k output == (state_next, out_next)))
      (decreases v j - v i)
  = if i =. j then
      lemma_squeeze_blocks_unfold output_len state rate i k output
    else begin
      let state' : t_Array u64 (mk_usize 25) =
        Hacspec_sha3.Keccak_f.keccak_f state in
      let output' : t_Array u8 output_len =
        HS.squeeze_state output_len state' output (i *! rate) rate in
      lemma_squeeze_blocks_unfold output_len state rate i j output;
      lemma_squeeze_blocks_unfold output_len state rate i k output;
      lemma_squeeze_blocks_tail output_len state' rate (i +! mk_usize 1) j k output'
    end
#pop-options


(* ================================================================
   Structural unfold of [Hacspec_sha3.Sponge.squeeze]: exhibits the
   RHS in the same let-bound form used by the Rust impl's inline
   proof scaffolding, so the final ensures VC in
   [Libcrux_sha3.Generic_keccak.Portable.squeeze] can discharge by
   rewriting the spec application to this explicit structure.
   Trivial at [fuel 1 ifuel 1] — Z3 unfolds [HS.squeeze] once.
   ================================================================ *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let lemma_squeeze_unfold
      (output_len: usize)
      (state: t_Array u64 (mk_usize 25))
      (rate: usize)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v output_len < v Core_models.Num.impl_usize__MAX - 200)
      (ensures (
        let output_blocks = output_len /! rate in
        let output_rem = output_len %! rate in
        let zeros : t_Array u8 output_len =
          Rust_primitives.Hax.repeat (mk_u8 0) output_len in
        HS.squeeze output_len state rate ==
          (if output_blocks =. mk_usize 0 then
             HS.squeeze_state output_len state zeros (mk_usize 0) output_len
           else
             let out0 =
               HS.squeeze_state output_len state zeros (mk_usize 0) rate in
             let (spec_st, spec_out) =
               HS.squeeze_blocks output_len state rate (mk_usize 1)
                 output_blocks out0 in
             let (_, out_final) =
               HS.squeeze_last output_len spec_st spec_out rate output_rem in
             out_final)))
  = ()
#pop-options

(* Trivial transitive equality for closing the squeeze ensures VC. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let lemma_seq_trans
      (#output_len: usize)
      (output_seq: Seq.seq u8)
      (final_spec spec_result: t_Array u8 output_len)
  : Lemma
      (requires
        output_seq == (final_spec <: Seq.seq u8) /\
        final_spec == spec_result)
      (ensures
        output_seq == (spec_result <: Seq.seq u8))
  = ()
#pop-options

(* ================================================================
   Extensionality of [squeeze_last] at indices `< output_len -
   output_rem`: two calls with same [state] and outputs that agree on
   the preserved prefix yield equal byte sequences.  Used by the
   impl's final reconciliation to bridge squeeze_last applied to the
   impl's output-after-loop (which matches spec_out only at the
   prefix) with squeeze_last applied to spec_out directly.

   Takes [out1] as a slice and [out2] as an array so the caller can
   pass the impl's [t_Slice] directly without coercion.
   ================================================================ *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 200"
let lemma_squeeze_last_extensional
      (output_len: usize)
      (state: t_Array u64 (mk_usize 25))
      (out1: t_Slice u8{Seq.length out1 == v output_len})
      (out2: t_Array u8 output_len)
      (rate output_rem: usize)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v output_rem < v rate /\
        v output_rem <= v output_len /\
        v output_len < v Core_models.Num.impl_usize__MAX - 200 /\
        (forall (k: nat). k < v output_len - v output_rem ==>
           Seq.index out1 k == Seq.index out2 k))
      (ensures (
        let out1_arr : t_Array u8 output_len = out1 in
        let (_, r1) = HS.squeeze_last output_len state out1_arr rate output_rem in
        let (_, r2) = HS.squeeze_last output_len state out2 rate output_rem in
        (r1 <: Seq.seq u8) == (r2 <: Seq.seq u8)))
  = let out1_arr : t_Array u8 output_len = out1 in
    let (_, r1) = HS.squeeze_last output_len state out1_arr rate output_rem in
    let (_, r2) = HS.squeeze_last output_len state out2 rate output_rem in
    if output_rem =. mk_usize 0 then
      Seq.lemma_eq_intro (r1 <: Seq.seq u8) (r2 <: Seq.seq u8)
    else begin
      let state' = Hacspec_sha3.Keccak_f.keccak_f state in
      let aux (k: nat{k < v output_len})
        : Lemma (Seq.index (r1 <: Seq.seq u8) k ==
                 Seq.index (r2 <: Seq.seq u8) k) =
        let i : usize = mk_usize k in
        assert (v i == k);
        if k < v output_len - v output_rem then
          ()
        else
          assert ((v i - (v output_len - v output_rem)) / 8 < 25)
      in
      FStar.Classical.forall_intro aux;
      Seq.lemma_eq_intro (r1 <: Seq.seq u8) (r2 <: Seq.seq u8)
    end
#pop-options
