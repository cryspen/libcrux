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
