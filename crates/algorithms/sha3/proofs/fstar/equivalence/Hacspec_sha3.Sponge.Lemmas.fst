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


(* ================================================================
   Absorb-side helpers about [Hacspec_sha3.Sponge.absorb_blocks].

   [absorb_blocks] mirrors [squeeze_blocks]: a tail-recursive helper
   over a block index in [i..input_blocks), applying [absorb_block]
   to each [input[k*rate..(k+1)*rate]].  Used by the impl's absorb
   inline loop invariant to avoid slice-of-slice reasoning (which
   triggers a Z3 4.13.3 LP-solver bug in the older [absorb_rec]-based
   proof).
   ================================================================ *)

(* Base case: [absorb_blocks state rate i i input == state]. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"
let lemma_absorb_blocks_base
      (state: t_Array u64 (mk_usize 25))
      (rate i: usize)
      (input: t_Slice u8)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v i <= Seq.length #u8 input / v rate)
      (ensures HS.absorb_blocks state rate i i input == state)
  = ()
#pop-options

(* Head-unfold of [absorb_blocks] at index [i < input_blocks]. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let lemma_absorb_blocks_unfold
      (state: t_Array u64 (mk_usize 25))
      (rate i input_blocks: usize)
      (input: t_Slice u8)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v i < v input_blocks /\
        v input_blocks * v rate <= Seq.length #u8 input)
      (ensures (
        let block : t_Slice u8 =
          input.[ { Core_models.Ops.Range.f_start = i *! rate;
                    Core_models.Ops.Range.f_end   = i *! rate +! rate } <:
                  Core_models.Ops.Range.t_Range usize ] in
        let state' = HS.absorb_block state block rate in
        HS.absorb_blocks state rate i input_blocks input ==
        HS.absorb_blocks state' rate (i +! mk_usize 1) input_blocks input))
  = FStar.Math.Lemmas.lemma_div_le
      (v input_blocks * v rate) (Seq.length #u8 input) (v rate);
    FStar.Math.Lemmas.cancel_mul_div (v input_blocks) (v rate)
#pop-options

(* Tail-extension of [absorb_blocks]: extend a run ending at [j] to
   one ending at [k == j+1].  Mirrors [lemma_squeeze_blocks_tail]. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 300"
let rec lemma_absorb_blocks_tail
      (state: t_Array u64 (mk_usize 25))
      (rate i j k: usize)
      (input: t_Slice u8)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v i <= v j /\
        v k == v j + 1 /\
        v k <= Seq.length #u8 input / v rate)
      (ensures (
        let state_j = HS.absorb_blocks state rate i j input in
        let block : t_Slice u8 =
          input.[ { Core_models.Ops.Range.f_start = j *! rate;
                    Core_models.Ops.Range.f_end   = j *! rate +! rate } <:
                  Core_models.Ops.Range.t_Range usize ] in
        let state_next = HS.absorb_block state_j block rate in
        HS.absorb_blocks state rate i k input == state_next))
      (decreases v j - v i)
  = if i =. j then
      lemma_absorb_blocks_unfold state rate i k input
    else begin
      let block_i : t_Slice u8 =
        input.[ { Core_models.Ops.Range.f_start = i *! rate;
                  Core_models.Ops.Range.f_end   = i *! rate +! rate } <:
                Core_models.Ops.Range.t_Range usize ] in
      let state' = HS.absorb_block state block_i rate in
      lemma_absorb_blocks_unfold state rate i j input;
      lemma_absorb_blocks_unfold state rate i k input;
      lemma_absorb_blocks_tail state' rate (i +! mk_usize 1) j k input
    end
#pop-options


(* ================================================================
   Bridge between [absorb_rec] (slice-tail recursion, the
   spec-facing form) and [absorb_blocks] + [absorb_final] (indexed,
   the impl-facing form):

     absorb_rec state rate delim input
     ==
     absorb_final (absorb_blocks state rate 0 input_blocks input)
                  input (input_blocks * rate) input_rem rate delim

   Proved by induction on [input_blocks] (== [input.len() / rate]).
   This is the only slicing-heavy proof in the absorb chain; it
   happens outside any loop context so the Z3 LP-solver
   instantiation bug doesn't trigger.
   ================================================================ *)

(* Helper: one recurrence step of [absorb_rec] when enough bytes
   remain (i.e. [input.len() >= rate]).  Stated on pure [Seq.slice]
   for a clean arithmetic precondition. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let lemma_absorb_rec_unfold
      (state: t_Array u64 (mk_usize 25))
      (rate: usize) (delim: u8)
      (input: t_Slice u8)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        Seq.length #u8 input >= v rate)
      (ensures (
        let block_0 : t_Slice u8 =
          input.[ { Core_models.Ops.Range.f_start = mk_usize 0;
                    Core_models.Ops.Range.f_end   = rate } <:
                  Core_models.Ops.Range.t_Range usize ] in
        let state' = HS.absorb_block state block_0 rate in
        let tail : t_Slice u8 =
          input.[ { Core_models.Ops.Range.f_start = rate } <:
                  Core_models.Ops.Range.t_RangeFrom usize ] in
        HS.absorb_rec state rate delim input ==
        HS.absorb_rec state' rate delim tail))
  = ()
#pop-options

(* Helper: slice of a RangeFrom suffix is the same as the corresponding
   slice of the original.  Used inside the induction step of
   [lemma_absorb_blocks_shift] to align block-boundaries between the
   two sides.  Proved by [FStar.Seq.Properties.slice_slice]. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"
let lemma_tail_block_eq_input_block
      (input: t_Slice u8)
      (rate n: usize)
  : Lemma
      (requires
        v rate > 0 /\
        Seq.length #u8 input >= v rate /\
        v n * v rate + v rate <= Seq.length #u8 input - v rate)
      (ensures (
        let tail : t_Slice u8 =
          input.[ { Core_models.Ops.Range.f_start = rate } <:
                  Core_models.Ops.Range.t_RangeFrom usize ] in
        let tail_block : t_Slice u8 =
          tail.[ { Core_models.Ops.Range.f_start = n *! rate;
                   Core_models.Ops.Range.f_end   = n *! rate +! rate } <:
                 Core_models.Ops.Range.t_Range usize ] in
        let input_block : t_Slice u8 =
          input.[ { Core_models.Ops.Range.f_start = (n +! mk_usize 1) *! rate;
                    Core_models.Ops.Range.f_end   = (n +! mk_usize 1) *! rate +! rate } <:
                  Core_models.Ops.Range.t_Range usize ] in
        tail_block == input_block))
  = FStar.Seq.Properties.slice_slice input
      (v rate) (Seq.length #u8 input) (v n * v rate) (v n * v rate + v rate)
#pop-options

(* Shift: absorbing [0..k+1) blocks from [input] starting at [state]
   equals absorbing [0..k) blocks from [tail] starting at [state']
   where [state' = absorb_block state input[0..rate] rate] and
   [tail = input[rate..]].

   Proved by induction on [k], stepping both sides with
   [lemma_absorb_blocks_tail] and aligning the block slices with
   [lemma_tail_block_eq_input_block]. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 300 --split_queries always"
let rec lemma_absorb_blocks_shift
      (state: t_Array u64 (mk_usize 25))
      (rate: usize)
      (k: usize)
      (input: t_Slice u8)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        Seq.length #u8 input >= v rate /\
        v k <= (Seq.length #u8 input - v rate) / v rate)
      (ensures (
        let block_0 : t_Slice u8 =
          input.[ { Core_models.Ops.Range.f_start = mk_usize 0;
                    Core_models.Ops.Range.f_end   = rate } <:
                  Core_models.Ops.Range.t_Range usize ] in
        let state' = HS.absorb_block state block_0 rate in
        let tail : t_Slice u8 =
          input.[ { Core_models.Ops.Range.f_start = rate } <:
                  Core_models.Ops.Range.t_RangeFrom usize ] in
        HS.absorb_blocks state rate (mk_usize 0) (k +! mk_usize 1) input ==
        HS.absorb_blocks state' rate (mk_usize 0) k tail))
      (decreases v k)
  = let block_0 : t_Slice u8 =
      input.[ { Core_models.Ops.Range.f_start = mk_usize 0;
                Core_models.Ops.Range.f_end   = rate } <:
              Core_models.Ops.Range.t_Range usize ] in
    let state' = HS.absorb_block state block_0 rate in
    let tail : t_Slice u8 =
      input.[ { Core_models.Ops.Range.f_start = rate } <:
              Core_models.Ops.Range.t_RangeFrom usize ] in
    if k =. mk_usize 0 then begin
      (* Base case k=0:
         LHS = absorb_blocks state rate 0 1 input.  Step once via tail lemma
         at i=j=0, k=1 to get absorb_block state input[0..rate] rate = state'.
         RHS = absorb_blocks state' rate 0 0 tail = state' (base). *)
      lemma_absorb_blocks_base state rate (mk_usize 0) input;
      lemma_absorb_blocks_tail state rate (mk_usize 0) (mk_usize 0)
        (mk_usize 1) input;
      lemma_absorb_blocks_base state' rate (mk_usize 0) tail
    end else begin
      let km1 : usize = k -! mk_usize 1 in
      let state_ih = HS.absorb_blocks state rate (mk_usize 0) k input in
      let state_tail_km1 = HS.absorb_blocks state' rate (mk_usize 0) km1 tail in
      (* Step LHS: absorb_blocks state rate 0 (k+1) input
                == absorb_block (absorb_blocks state rate 0 k input) input[k*rate..(k+1)*rate] rate *)
      lemma_absorb_blocks_tail state rate (mk_usize 0) k (k +! mk_usize 1) input;
      let input_block_k : t_Slice u8 =
        input.[ { Core_models.Ops.Range.f_start = k *! rate;
                  Core_models.Ops.Range.f_end   = k *! rate +! rate } <:
                Core_models.Ops.Range.t_Range usize ] in
      assert (HS.absorb_blocks state rate (mk_usize 0) (k +! mk_usize 1) input ==
              HS.absorb_block state_ih input_block_k rate);
      (* Step RHS: absorb_blocks state' rate 0 k tail
                == absorb_block (absorb_blocks state' rate 0 km1 tail) tail[km1*rate..k*rate] rate *)
      lemma_absorb_blocks_tail state' rate (mk_usize 0) km1 k tail;
      let tail_block_km1 : t_Slice u8 =
        tail.[ { Core_models.Ops.Range.f_start = km1 *! rate;
                 Core_models.Ops.Range.f_end   = km1 *! rate +! rate } <:
               Core_models.Ops.Range.t_Range usize ] in
      assert (HS.absorb_blocks state' rate (mk_usize 0) k tail ==
              HS.absorb_block state_tail_km1 tail_block_km1 rate);
      (* IH: state_ih == state_tail_km1 *)
      lemma_absorb_blocks_shift state rate km1 input;
      assert (state_ih == state_tail_km1);
      (* Align the block slices: tail[km1*rate..k*rate] == input[k*rate..(k+1)*rate].
         Note (km1 +! 1) *! rate == k *! rate; the lemma uses (n+1)*rate on the
         input side, so with n = km1 we get input[k*rate..k*rate+rate]. *)
      lemma_tail_block_eq_input_block input rate km1;
      assert (Seq.equal (tail_block_km1 <: Seq.seq u8)
                        (input_block_k <: Seq.seq u8));
      (* The two t_Slice values equal as Seq, so absorb_block on them matches. *)
      assert (HS.absorb_block state_ih input_block_k rate ==
              HS.absorb_block state_tail_km1 tail_block_km1 rate)
    end
#pop-options


(* Helper: the bytes read by [pad_last_block] from [tail] starting at
   [start] equal the bytes read from [input] starting at [rate+start].
   This makes the two [absorb_final] calls in [lemma_absorb_rec_via_blocks]'s
   inductive step equal. *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 100"
let lemma_absorb_final_shift
      (state: t_Array u64 (mk_usize 25))
      (rate: usize) (delim: u8)
      (input: t_Slice u8)
      (start rem: usize)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        Seq.length #u8 input >= v rate /\
        v rem < v rate /\
        v start + v rem <= Seq.length #u8 input - v rate)
      (ensures (
        let tail : t_Slice u8 =
          input.[ { Core_models.Ops.Range.f_start = rate } <:
                  Core_models.Ops.Range.t_RangeFrom usize ] in
        HS.absorb_final state tail start rem rate delim ==
        HS.absorb_final state input (rate +! start) rem rate delim))
  = let tail : t_Slice u8 =
      input.[ { Core_models.Ops.Range.f_start = rate } <:
              Core_models.Ops.Range.t_RangeFrom usize ] in
    (* pad_last_block reads message[msg_offset..msg_offset+remaining].  The
       two resulting buffers agree on positions [0..remaining], and both
       sides apply the same delim byte at [remaining] and terminator at
       [rate-1]; Seq.equal follows. *)
    FStar.Seq.Properties.slice_slice input
      (v rate) (Seq.length #u8 input) (v start) (v start + v rem);
    let b1 = HS.pad_last_block tail start rem rate delim in
    let b2 = HS.pad_last_block input (rate +! start) rem rate delim in
    assert (Seq.equal (b1 <: Seq.seq u8) (b2 <: Seq.seq u8));
    assert (b1 == b2)
#pop-options


#push-options "--fuel 1 --ifuel 1 --z3rlimit 300"
let rec lemma_absorb_rec_via_blocks
      (state: t_Array u64 (mk_usize 25))
      (rate: usize) (delim: u8)
      (input: t_Slice u8)
  : Lemma
      (requires Libcrux_sha3.Proof_utils.valid_rate rate)
      (ensures (
        let input_len : usize = Core_models.Slice.impl__len #u8 input in
        let input_blocks : usize = input_len /! rate in
        let input_rem : usize = input_len %! rate in
        let state_k = HS.absorb_blocks state rate (mk_usize 0) input_blocks input in
        HS.absorb_rec state rate delim input ==
        HS.absorb_final state_k input (input_len -! input_rem) input_rem rate delim))
      (decreases Seq.length #u8 input)
  = let input_len : usize = Core_models.Slice.impl__len #u8 input in
    let input_blocks : usize = input_len /! rate in
    let input_rem : usize = input_len %! rate in
    if v input_len < v rate then begin
      (* Base case: input_blocks = 0, input_rem = input_len.
         LHS unfolds directly: absorb_rec state rate delim input
                               = absorb_final state input 0 input_len rate delim
         RHS: absorb_blocks state rate 0 0 input == state (by base),
              so RHS = absorb_final state input 0 input_len rate delim *)
      lemma_absorb_blocks_base state rate (mk_usize 0) input
    end else begin
      let block_0 : t_Slice u8 =
        input.[ { Core_models.Ops.Range.f_start = mk_usize 0;
                  Core_models.Ops.Range.f_end   = rate } <:
                Core_models.Ops.Range.t_Range usize ] in
      let state' = HS.absorb_block state block_0 rate in
      let tail : t_Slice u8 =
        input.[ { Core_models.Ops.Range.f_start = rate } <:
                Core_models.Ops.Range.t_RangeFrom usize ] in
      let tail_len : usize = Core_models.Slice.impl__len #u8 tail in
      let tail_blocks : usize = tail_len /! rate in
      let tail_rem : usize = tail_len %! rate in
      (* Arithmetic: tail_len = input_len - rate,
                     tail_blocks = input_blocks - 1,
                     tail_rem = input_rem *)
      assert (v tail_len == v input_len - v rate);
      FStar.Math.Lemmas.lemma_div_plus (v input_len - v rate) 1 (v rate);
      assert (v tail_blocks == v input_blocks - 1);
      FStar.Math.Lemmas.modulo_addition_lemma (v input_len - v rate) (v rate) 1;
      assert (v tail_rem == v input_rem);
      (* IH on tail (decreases: tail_len = input_len - rate < input_len). *)
      lemma_absorb_rec_via_blocks state' rate delim tail;
      (* Bridge 1: absorb_blocks state' rate 0 tail_blocks tail
                == absorb_blocks state rate 0 input_blocks input *)
      lemma_absorb_blocks_shift state rate tail_blocks input;
      (* Bridge 2: align the absorb_final offset between tail-view and input-view.
         tail offset = tail_blocks * rate = (input_blocks - 1) * rate
         input offset = input_blocks * rate = rate + (input_blocks - 1) * rate *)
      let final_offset_tail : usize = tail_blocks *! rate in
      let final_offset_input : usize = input_blocks *! rate in
      assert (v final_offset_input == v rate + v final_offset_tail);
      let state_k = HS.absorb_blocks state rate (mk_usize 0) input_blocks input in
      lemma_absorb_final_shift state_k rate delim input final_offset_tail tail_rem
    end
#pop-options
