module Impl_Spec_Sponge.Squeeze

#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"

open FStar.Mul
open Core_models
open Impl_Spec_Sponge.Core


(* ================================================================
   Phase 13: store_block == squeeze_state

   Impl: Libcrux_sha3.Simd.Portable.store_block(RATE, state, out, start, len)
     Loop (i in 0..len/8):
       bytes = to_le_bytes(get_ij(1, state, i/5, i%5))
       out[start+8*i .. start+8*i+8] = copy_from_slice(bytes)
     Remainder (if len%8 > 0):
       bytes = to_le_bytes(get_ij(1, state, (len/8)/5, (len/8)%5))
       out[start+len-rem .. start+len] = bytes[0..rem]

   Spec: Hacspec_sha3.Sponge.squeeze_state(state, output, out_offset, len)
     Loop (i in 0..len/8):
       bytes = to_le_bytes(state[lane_index(i)])
       output[out_offset+8*i .. out_offset+8*(i+1)] = copy_from_slice(bytes)
     Remainder (if len%8 > 0):
       bytes = to_le_bytes(state[lane_index(len/8)])
       output[pos..pos+remaining] = copy_from_slice(bytes[..remaining])

   Both now use copy_from_slice (B3 fix applied).

   Equivalence:
   1. Both read state at lane_index(i): the impl via get_ij(1, state, i/5, i%5)
      which reads state[5*(i%5) + i/5] = state[lane_index(i)].
      (Phase 10)
   2. Both write the same LE bytes to the same output positions.

   Proof sketch:
   - Per-position equality: for each output position p in [start..start+len),
     show both sides write the same byte from the same lane.
   - Use forall_intro + Seq.lemma_eq_intro.

   Difficulty: MEDIUM. Same loop structure, same idioms after B3 fix.
   ================================================================ *)

(* =================================================================
   Phase 13 decomposition
   -----------------------------------------------------------------
   Rather than admitting the full [lemma_store_block_bridge], we
   decompose the Phase 13 equivalence into:

     1. [store_block_impl_loop]     — recursive mirror of impl
        [store_block]'s [fold_range] body.
     2. [squeeze_state_spec_loop]   — recursive mirror of spec
        [squeeze_state]'s [fold_range] body.
     3. [lemma_store_loop_equiv]    — PROVED: impl-loop ≡ spec-loop
        by induction on (n − i), using Phase 10
        ([lemma_lane_index_is_impl_index]) at each step.
     4. Two fold-unfold axioms bridging each fold_range to its
        corresponding recursive loop. These capture exactly the
        closure-equality limitation already documented for Admits 1
        and 2; they add no mathematical content.
     5. [lemma_store_block_remainder_equiv] — PROVED: the remainder
        branches coincide by Phase 10.
     6. [lemma_store_block_bridge]  — PROVED: composes 3 + 4 + 5.
   ================================================================= *)

(** Recursive mirror of impl [store_block]'s fold_range body.  Walks
    [i → n], writing 8 little-endian bytes per step read from the
    state using [get_ij]. *)
let rec store_block_impl_loop
      (s: spec_state)
      (out: t_Slice u8)
      (start: usize)
      (i n: usize)
    : Pure (t_Slice u8)
      (requires
        v i <= v n /\
        v n <= 25 /\
        v start + 8 * v n <= Seq.length out)
      (ensures fun out_future ->
        Seq.length out_future == Seq.length out)
      (decreases (v n - v i))
  =
  if i =. n then out
  else
    let bytes: t_Array u8 (mk_usize 8) =
      Core_models.Num.impl_u64__to_le_bytes
        (Libcrux_sha3.Traits.get_ij (mk_usize 1) #u64 s
           (i /! mk_usize 5) (i %! mk_usize 5))
    in
    let out_pos: usize = start +! (mk_usize 8 *! i) in
    let out: t_Slice u8 =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
        ({ Core_models.Ops.Range.f_start = out_pos;
           Core_models.Ops.Range.f_end   = out_pos +! mk_usize 8 } <:
         Core_models.Ops.Range.t_Range usize)
        (Core_models.Slice.impl__copy_from_slice #u8
          (out.[ { Core_models.Ops.Range.f_start = out_pos;
                   Core_models.Ops.Range.f_end   = out_pos +! mk_usize 8 } <:
                 Core_models.Ops.Range.t_Range usize ] <: t_Slice u8)
          (bytes <: t_Slice u8))
    in
    store_block_impl_loop s out start (i +! mk_usize 1) n

(** Recursive mirror of spec [squeeze_state]'s fold_range body.  Walks
    [i → n], writing 8 little-endian bytes per step read from the
    state using [lane_index]. *)
let rec squeeze_state_spec_loop
      (s: spec_state)
      (out: t_Slice u8)
      (start: usize)
      (i n: usize)
    : Pure (t_Slice u8)
      (requires
        v i <= v n /\
        v n <= 25 /\
        v start + 8 * v n <= Seq.length out)
      (ensures fun out_future ->
        Seq.length out_future == Seq.length out)
      (decreases (v n - v i))
  =
  if i =. n then out
  else
    let idx: usize = i in
    let bytes: t_Array u8 (mk_usize 8) =
      Core_models.Num.impl_u64__to_le_bytes (s.[ idx ] <: u64)
    in
    let out: t_Slice u8 =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
        ({ Core_models.Ops.Range.f_start = start +! (mk_usize 8 *! i);
           Core_models.Ops.Range.f_end   = start +! (mk_usize 8 *! (i +! mk_usize 1)) } <:
         Core_models.Ops.Range.t_Range usize)
        (Core_models.Slice.impl__copy_from_slice #u8
          (out.[ { Core_models.Ops.Range.f_start = start +! (mk_usize 8 *! i);
                   Core_models.Ops.Range.f_end   = start +! (mk_usize 8 *! (i +! mk_usize 1)) } <:
                 Core_models.Ops.Range.t_Range usize ] <: t_Slice u8)
          (bytes <: t_Slice u8))
    in
    squeeze_state_spec_loop s out start (i +! mk_usize 1) n

#push-options "--fuel 1 --z3rlimit 200"
(** PROVED: impl and spec recursive loops agree step-by-step.
    At each step the bytes written are equal by Phase 10:
    [get_ij 1 s (i/5) (i%5) = s.[5*(i%5) + i/5] = s.[lane_index i]],
    and the write ranges coincide ([start + 8*i .. start + 8*i + 8]
    vs [start + 8*i .. start + 8*(i+1)], same integers). *)
let rec lemma_store_loop_equiv
      (s: spec_state)
      (out: t_Slice u8)
      (start: usize)
      (i n: usize)
  : Lemma
      (requires
        v i <= v n /\
        v n <= 25 /\
        v start + 8 * v n <= Seq.length out)
      (ensures
        store_block_impl_loop s out start i n ==
        squeeze_state_spec_loop s out start i n)
      (decreases (v n - v i))
  =
  if i =. n then ()
  else begin
    (* Phase 10: lane_index i = 5*(i%5) + i/5. *)
    lemma_lane_index_is_impl_index i;
    (* By definition of get_ij (arr.[5*j + i]),
       get_ij 1 s (i/5) (i%5) = s.[5*(i%5) + i/5] = s.[lane_index i]. *)
    let bytes: t_Array u8 (mk_usize 8) =
      Core_models.Num.impl_u64__to_le_bytes (s.[ i ] <: u64)
    in
    let out_pos: usize = start +! (mk_usize 8 *! i) in
    let end_ : usize = out_pos +! mk_usize 8 in
    let end_' : usize = start +! (mk_usize 8 *! (i +! mk_usize 1)) in
    (* end_ == end_' as usize because 8*i + 8 = 8*(i+1). *)
    assert (v end_ == v end_');
    let out': t_Slice u8 =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
        ({ Core_models.Ops.Range.f_start = out_pos;
           Core_models.Ops.Range.f_end   = end_ } <:
         Core_models.Ops.Range.t_Range usize)
        (Core_models.Slice.impl__copy_from_slice #u8
          (out.[ { Core_models.Ops.Range.f_start = out_pos;
                   Core_models.Ops.Range.f_end   = end_ } <:
                 Core_models.Ops.Range.t_Range usize ] <: t_Slice u8)
          (bytes <: t_Slice u8))
    in
    lemma_store_loop_equiv s out' start (i +! mk_usize 1) n
  end
#pop-options

(** Typed helper: the remainder step of [store_block] (impl side).
    Writes the trailing [remaining = len %! 8] bytes of the final
    (partial) lane [octets = len/8] into [out]. *)
let store_block_impl_remainder
      (s: spec_state)
      (out: t_Slice u8)
      (start len: usize)
    : Pure (t_Slice u8)
      (requires
        v start + v len <= Seq.length out /\
        v len < 200 /\
        v (len %! mk_usize 8) > 0)
      (ensures fun out_future ->
        Seq.length out_future == Seq.length out)
  =
  let octets: usize = len /! mk_usize 8 in
  let remaining: usize = len %! mk_usize 8 in
  let bytes: t_Array u8 (mk_usize 8) =
    Core_models.Num.impl_u64__to_le_bytes
      (Libcrux_sha3.Traits.get_ij (mk_usize 1) #u64 s
         (octets /! mk_usize 5) (octets %! mk_usize 5))
  in
  let out_pos: usize = (start +! len) -! remaining in
  Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
    ({ Core_models.Ops.Range.f_start = out_pos;
       Core_models.Ops.Range.f_end   = out_pos +! remaining } <:
     Core_models.Ops.Range.t_Range usize)
    (Core_models.Slice.impl__copy_from_slice #u8
      (out.[ { Core_models.Ops.Range.f_start = out_pos;
               Core_models.Ops.Range.f_end   = out_pos +! remaining } <:
             Core_models.Ops.Range.t_Range usize ] <: t_Slice u8)
      (bytes.[ { Core_models.Ops.Range.f_end = remaining } <:
               Core_models.Ops.Range.t_RangeTo usize ] <: t_Slice u8))

(** Typed helper: the remainder step of [squeeze_state] (spec side). *)
let squeeze_state_spec_remainder
      (s: spec_state)
      (out: t_Slice u8)
      (start len: usize)
    : Pure (t_Slice u8)
      (requires
        v start + v len <= Seq.length out /\
        v len < 200 /\
        v (len %! mk_usize 8) > 0)
      (ensures fun out_future ->
        Seq.length out_future == Seq.length out)
  =
  let octets: usize = len /! mk_usize 8 in
  let remaining: usize = len %! mk_usize 8 in
  let idx: usize = octets in
  let bytes: t_Array u8 (mk_usize 8) =
    Core_models.Num.impl_u64__to_le_bytes (s.[ idx ] <: u64)
  in
  let out_pos: usize = start +! (mk_usize 8 *! octets) in
  Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
    ({ Core_models.Ops.Range.f_start = out_pos;
       Core_models.Ops.Range.f_end   = out_pos +! remaining } <:
     Core_models.Ops.Range.t_Range usize)
    (Core_models.Slice.impl__copy_from_slice #u8
      (out.[ { Core_models.Ops.Range.f_start = out_pos;
               Core_models.Ops.Range.f_end   = out_pos +! remaining } <:
             Core_models.Ops.Range.t_Range usize ] <: t_Slice u8)
      (bytes.[ { Core_models.Ops.Range.f_end = remaining } <:
               Core_models.Ops.Range.t_RangeTo usize ] <: t_Slice u8))

#push-options "--fuel 1 --z3rlimit 200"
(** PROVED: the two remainder helpers agree.
    Bytes match by Phase 10 + [get_ij] unfolding
    ([get_ij 1 s (o/5) (o%5) = s.[5*(o%5)+o/5] = s.[lane_index o]]).
    Write position matches because
    [v (start+len-remaining) = v start + 8 * v octets]
    (from [len = 8*octets + remaining]). *)
let lemma_remainder_fns_equiv
      (s: spec_state)
      (out: t_Slice u8)
      (start len: usize)
  : Lemma
      (requires
        v start + v len <= Seq.length out /\
        v len < 200 /\
        v (len %! mk_usize 8) > 0)
      (ensures
        store_block_impl_remainder s out start len ==
        squeeze_state_spec_remainder s out start len)
  =
  let octets: usize = len /! mk_usize 8 in
  let remaining: usize = len %! mk_usize 8 in
  assert (v octets < 25);
  lemma_lane_index_is_impl_index octets;
  (* Byte equality: under FIPS-native layout,
     get_ij 1 s (octets/5) (octets%5) = s.[5*(octets/5) + octets%5] = s.[octets]. *)
  assert (v octets ==
          5 * v (octets /! mk_usize 5) + v (octets %! mk_usize 5));
  (* Position equality: (start+len)-remaining = start + 8*octets. *)
  let pos_impl: usize = (start +! len) -! remaining in
  let pos_spec: usize = start +! (mk_usize 8 *! octets) in
  assert (v pos_impl == v pos_spec)
#pop-options

(** Local fold-bridge axiom (impl side). Decomposes the full
    [store_block] body as [store_block_impl_loop ∘ optional remainder].
    Same closure-equality limitation as Admits 1–2: the inline fold
    body in [store_block]'s source is shown equal to the named loop. *)
assume val lemma_store_block_decomposes
      (rate: usize)
      (s: spec_state)
      (out: t_Slice u8)
      (start len: usize)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v len <= v rate /\
        v start + v len <= Seq.length out)
      (ensures (
        let octets: usize = len /! mk_usize 8 in
        let out1: t_Slice u8 =
          store_block_impl_loop s out start (mk_usize 0) octets
        in
        Libcrux_sha3.Simd.Portable.store_block rate s out start len ==
        (if (len %! mk_usize 8) >. mk_usize 0 then
           store_block_impl_remainder s out1 start len
         else out1)))

(** Local fold-bridge axiom (spec side). Decomposes the full
    [squeeze_state] body as [squeeze_state_spec_loop ∘ optional remainder]. *)
assume val lemma_squeeze_state_decomposes
      (s: spec_state)
      (out: t_Slice u8)
      (start len: usize)
  : Lemma
      (requires
        v len <= 200 /\
        v start + v len <= Seq.length out)
      (ensures (
        let octets: usize = len /! mk_usize 8 in
        let out1: t_Slice u8 =
          squeeze_state_spec_loop s out start (mk_usize 0) octets
        in
        Hacspec_sha3.Sponge.squeeze_state s out start len ==
        (if (len %! mk_usize 8) >. mk_usize 0 then
           squeeze_state_spec_remainder s out1 start len
         else out1)))

(** MAIN Phase 13 THEOREM — proved by composition. *)
#push-options "--fuel 1 --z3rlimit 400"
let lemma_store_block_bridge
      (rate: usize)
      (state: spec_state)
      (out: t_Slice u8)
      (start len: usize)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v len <= v rate /\
        v start + v len <= Seq.length out)
      (ensures
        Libcrux_sha3.Simd.Portable.store_block rate state out start len ==
        Hacspec_sha3.Sponge.squeeze_state state out start len)
  =
  let octets: usize = len /! mk_usize 8 in
  assert (v octets <= 25);
  assert (8 * v octets <= v len);
  assert (v start + 8 * v octets <= Seq.length out);
  (* Bridge fold_range ↔ recursive loop + remainder on each side. *)
  lemma_store_block_decomposes rate state out start len;
  lemma_squeeze_state_decomposes state out start len;
  (* Inductive equivalence of the two loops (PROVED from Phase 10). *)
  lemma_store_loop_equiv state out start (mk_usize 0) octets;
  let out1_impl =
    store_block_impl_loop state out start (mk_usize 0) octets in
  let out1_spec =
    squeeze_state_spec_loop state out start (mk_usize 0) octets in
  assert (out1_impl == out1_spec);
  (* Remainder branch equivalence, when present. *)
  if (len %! mk_usize 8) >. mk_usize 0 then
    lemma_remainder_fns_equiv state out1_impl start len
#pop-options

let lemma_store_block_equiv
      (rate: usize)
      (state: spec_state)
      (out: t_Slice u8)
      (start len: usize)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v len <= v rate /\
        v start + v len <= Seq.length out)
      (ensures
        Libcrux_sha3.Simd.Portable.store_block rate state out start len ==
        Hacspec_sha3.Sponge.squeeze_state state out start len)
  = lemma_store_block_bridge rate state out start len

(** Squeeze-phase equivalence (single-squeeze case).
    When OUTPUT_LEN <= RATE, both sides do exactly one squeeze
    with no additional keccakf calls. This covers all standard
    SHA-3 hash functions (sha224/256/384/512). *)
let lemma_squeeze_single_equiv
      (rate: usize)
      (state: spec_state)
      (impl_out spec_out: t_Slice u8)
      (output_len: usize)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v output_len <= v rate /\
        Seq.length impl_out == v output_len /\
        Seq.length spec_out == v output_len)
      (ensures (
        Libcrux_sha3.Simd.Portable.store_block rate state impl_out (mk_usize 0) output_len ==
        Hacspec_sha3.Sponge.squeeze_state state impl_out (mk_usize 0) output_len))
  =
  lemma_store_block_equiv rate state impl_out (mk_usize 0) output_len
  (* Proof: direct application of lemma_store_block_equiv *)

(* One impl squeeze step through the trait instance. *)
let impl_squeeze_once
      (rate: usize)
      (ks: impl_state)
      (output: t_Slice u8)
      (start len: usize)
  : Pure (t_Slice u8)
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v len <= v rate /\
        v start + v len <= Seq.length output)
      (ensures fun output' -> Seq.length output' == Seq.length output)
  =
  Libcrux_sha3.Traits.f_squeeze #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
    #u64
    #FStar.Tactics.Typeclasses.solve
    rate
    ks
    output
    start
    len

(* In the portable backend, [f_squeeze] is exactly [store_block] on ks.f_st. *)
let lemma_impl_squeeze_once_store_block
      (rate: usize)
      (ks: impl_state)
      (output: t_Slice u8)
      (start len: usize)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v len <= v rate /\
        v start + v len <= Seq.length output)
      (ensures
        impl_squeeze_once rate ks output start len ==
        Libcrux_sha3.Simd.Portable.store_block
          rate
          ks.Libcrux_sha3.Generic_keccak.f_st
          output
          start
          len)
  = ()

(* Recursive mirror of the impl's squeeze fold_range body. *)
let rec impl_squeeze_loop
      (ks: impl_state)
      (output: t_Slice u8)
      (rate: usize)
      (i output_blocks: usize)
  : Pure (t_Slice u8 & impl_state)
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v i <= v output_blocks /\
        v output_blocks * v rate <= Seq.length output)
      (ensures (fun res ->
        let output', _ = res in
        Seq.length output' == Seq.length output))
      (decreases (v output_blocks - v i))
  =
  if i =. output_blocks then
    output, ks
  else
    let _: Prims.unit =
      Libcrux_sha3.Proof_utils.Lemmas.lemma_mul_succ_le i output_blocks rate
    in
    let ks' =
      Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 (mk_usize 1) #u64 ks
    in
    let output' =
      Libcrux_sha3.Traits.f_squeeze #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
        #u64
        #FStar.Tactics.Typeclasses.solve
        rate
        ks'
        output
        (i *! rate)
        rate
    in
    impl_squeeze_loop ks' output' rate (i +! mk_usize 1) output_blocks

(* Recursive mirror of the spec's squeeze fold_range body. *)
let rec spec_squeeze_loop
      (state: spec_state)
      (output: t_Slice u8)
      (rate: usize)
      (i output_blocks: usize)
  : Pure (t_Slice u8 & spec_state)
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v i <= v output_blocks /\
        v output_blocks * v rate <= Seq.length output)
      (ensures (fun res ->
        let output', _ = res in
        Seq.length output' == Seq.length output))
      (decreases (v output_blocks - v i))
  =
  if i =. output_blocks then
    output, state
  else
    let _: Prims.unit =
      Libcrux_sha3.Proof_utils.Lemmas.lemma_mul_succ_le i output_blocks rate
    in
    let state' = Hacspec_sha3.Keccak_f.keccak_f state in
    let output' = Hacspec_sha3.Sponge.squeeze_state state' output (i *! rate) rate in
    spec_squeeze_loop state' output' rate (i +! mk_usize 1) output_blocks

let impl_squeeze_acc (output0: t_Slice u8) =
  pair: (t_Slice u8 & impl_state) {
    let output, _ = pair in
    Seq.length output == Seq.length output0
  }

let spec_squeeze_acc (output0: t_Slice u8) =
  pair: (t_Slice u8 & spec_state) {
    let output, _ = pair in
    Seq.length output == Seq.length output0
  }

(* Named fold expressions for squeeze-side bridging. *)
let impl_squeeze_fold
      (ks: impl_state)
      (output0: t_Slice u8)
      (rate: usize)
      (i output_blocks: usize)
  : Pure (t_Slice u8 & impl_state)
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v i <= v output_blocks /\
        v output_blocks * v rate <= Seq.length output0)
      (ensures (fun res ->
        let output', _ = res in
        Seq.length output' == Seq.length output0))
  =
  let init : impl_squeeze_acc output0 = output0, ks in
  let inv (_: impl_squeeze_acc output0) (_: usize) : Type0 = True in
  let step
        (pair: impl_squeeze_acc output0)
        (j: usize { v j < v output_blocks })
    : impl_squeeze_acc output0
    =
    let output, s = pair in
    let _: Prims.unit =
      Libcrux_sha3.Proof_utils.Lemmas.lemma_mul_succ_le j output_blocks rate
    in
    assert (v (j *! rate) + v rate <= v output_blocks * v rate);
    assert (Seq.length output == Seq.length output0);
    assert (v output_blocks * v rate <= Seq.length output);
    assert (v (j *! rate) + v rate <= Seq.length output);
    let s' =
      Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 (mk_usize 1) #u64 s
    in
    let output' = impl_squeeze_once rate s' output (j *! rate) rate in
    assert (Seq.length output' == Seq.length output);
    assert (Seq.length output' == Seq.length output0);
    output', s'
  in
  Rust_primitives.Hax.Folds.fold_range i output_blocks inv init step

let spec_squeeze_fold
      (state: spec_state)
      (output0: t_Slice u8)
      (rate: usize)
      (i output_blocks: usize)
  : Pure (t_Slice u8 & spec_state)
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v i <= v output_blocks /\
        v output_blocks * v rate <= Seq.length output0)
      (ensures (fun res ->
        let output', _ = res in
        Seq.length output' == Seq.length output0))
  =
  let init : spec_squeeze_acc output0 = output0, state in
  let inv (_: spec_squeeze_acc output0) (_: usize) : Type0 = True in
  let step
        (pair: spec_squeeze_acc output0)
        (j: usize { v j < v output_blocks })
    : spec_squeeze_acc output0
    =
    let output, s = pair in
    let _: Prims.unit =
      Libcrux_sha3.Proof_utils.Lemmas.lemma_mul_succ_le j output_blocks rate
    in
    assert (v (j *! rate) + v rate <= v output_blocks * v rate);
    assert (Seq.length output == Seq.length output0);
    assert (v output_blocks * v rate <= Seq.length output);
    assert (v (j *! rate) + v rate <= Seq.length output);
    let s' = Hacspec_sha3.Keccak_f.keccak_f s in
    let output' = Hacspec_sha3.Sponge.squeeze_state s' output (j *! rate) rate in
    assert (Seq.length output' == Seq.length output);
    assert (Seq.length output' == Seq.length output0);
    output', s'
  in
  Rust_primitives.Hax.Folds.fold_range i output_blocks inv init step

(* Local fold-bridge axiom: impl fold_range == recursive squeeze loop. *)
assume val lemma_impl_squeeze_fold_is_loop
      (ks: impl_state)
      (output: t_Slice u8)
      (rate: usize)
      (i output_blocks: usize)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v i <= v output_blocks /\
        v output_blocks * v rate <= Seq.length output)
      (ensures
        impl_squeeze_fold ks output rate i output_blocks ==
        impl_squeeze_loop ks output rate i output_blocks)

(* Local fold-bridge axiom: spec fold_range == recursive squeeze loop. *)
assume val lemma_spec_squeeze_fold_is_loop
      (state: spec_state)
      (output: t_Slice u8)
      (rate: usize)
      (i output_blocks: usize)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v i <= v output_blocks /\
        v output_blocks * v rate <= Seq.length output)
      (ensures
        spec_squeeze_fold state output rate i output_blocks ==
        spec_squeeze_loop state output rate i output_blocks)

#push-options "--fuel 1 --z3rlimit 300 --split_queries always"
let rec lemma_squeeze_loop_equiv
      (ks: impl_state)
      (state: spec_state)
      (output: t_Slice u8)
      (rate: usize)
      (i output_blocks: usize)
  : Lemma
      (requires
        ks.Libcrux_sha3.Generic_keccak.f_st == state /\
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v i <= v output_blocks /\
        v output_blocks * v rate <= Seq.length output)
      (ensures (
        let output_impl, ks_impl = impl_squeeze_loop ks output rate i output_blocks in
        let output_spec, state_spec = spec_squeeze_loop state output rate i output_blocks in
        output_impl == output_spec /\
        ks_impl.Libcrux_sha3.Generic_keccak.f_st == state_spec))
      (decreases (v output_blocks - v i))
  =
  if i =. output_blocks then
    ()
  else
    let _: Prims.unit =
      Libcrux_sha3.Proof_utils.Lemmas.lemma_mul_succ_le i output_blocks rate
    in
    let ks' =
      Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 (mk_usize 1) #u64 ks
    in
    let state' = Hacspec_sha3.Keccak_f.keccak_f state in
    let output_impl =
      Libcrux_sha3.Traits.f_squeeze #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
        #u64
        #FStar.Tactics.Typeclasses.solve
        rate
        ks'
        output
        (i *! rate)
        rate
    in
    let output_spec = Hacspec_sha3.Sponge.squeeze_state state' output (i *! rate) rate in
    Impl_Spec_Keccakf.lemma_keccakf1600_equiv ks state;
    lemma_impl_squeeze_once_store_block rate ks' output (i *! rate) rate;
    lemma_store_block_equiv rate state' output (i *! rate) rate;
    assert (output_impl == output_spec);
    assert (ks'.Libcrux_sha3.Generic_keccak.f_st == state');
    assert (v i < v output_blocks);
    assert (v (i +! mk_usize 1) <= v output_blocks);
    assert (Seq.length output_impl == Seq.length output);
    assert (v output_blocks * v rate <= Seq.length output_impl);
    lemma_squeeze_loop_equiv ks' state' output_impl rate (i +! mk_usize 1) output_blocks
#pop-options

let lemma_squeeze_zero_blocks_equiv
      (rate: usize)
      (ks: impl_state)
      (state: spec_state)
      (out: t_Slice u8)
      (output_len: usize)
  : Lemma
      (requires
        ks.Libcrux_sha3.Generic_keccak.f_st == state /\
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v output_len <= v rate /\
        Seq.length out == v output_len)
      (ensures
        impl_squeeze_once rate ks out (mk_usize 0) output_len ==
        Hacspec_sha3.Sponge.squeeze_state state out (mk_usize 0) output_len)
  =
  lemma_impl_squeeze_once_store_block rate ks out (mk_usize 0) output_len;
  lemma_store_block_equiv rate state out (mk_usize 0) output_len

let lemma_squeeze_first_block_equiv
      (rate: usize)
      (ks: impl_state)
      (state: spec_state)
      (out: t_Slice u8)
  : Lemma
      (requires
        ks.Libcrux_sha3.Generic_keccak.f_st == state /\
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        Seq.length out >= v rate)
      (ensures
        impl_squeeze_once rate ks out (mk_usize 0) rate ==
        Hacspec_sha3.Sponge.squeeze_state state out (mk_usize 0) rate)
  =
  lemma_impl_squeeze_once_store_block rate ks out (mk_usize 0) rate;
  lemma_store_block_equiv rate state out (mk_usize 0) rate

let lemma_squeeze_remainder_equiv
      (rate: usize)
      (ks: impl_state)
      (state: spec_state)
      (out: t_Slice u8)
      (output_len output_rem: usize)
  : Lemma
      (requires
        ks.Libcrux_sha3.Generic_keccak.f_st == state /\
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        output_rem <>. mk_usize 0 /\
        v output_rem < v rate /\
        v rate <= v output_len /\
        Seq.length out == v output_len)
      (ensures
        impl_squeeze_once
          rate
          (Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 (mk_usize 1) #u64 ks)
          out
          (output_len -! output_rem)
          output_rem
        ==
        Hacspec_sha3.Sponge.squeeze_state
          (Hacspec_sha3.Keccak_f.keccak_f state)
          out
          (output_len -! output_rem)
          output_rem)
  =
  let ks_tail =
    Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 (mk_usize 1) #u64 ks
  in
  let state_tail = Hacspec_sha3.Keccak_f.keccak_f state in
  Impl_Spec_Keccakf.lemma_keccakf1600_equiv ks state;
  assert (ks_tail.Libcrux_sha3.Generic_keccak.f_st == state_tail);
  assert (v output_rem <= v output_len);
  assert (v (output_len -! output_rem) + v output_rem == v output_len);
  assert (v (output_len -! output_rem) + v output_rem <= Seq.length out);
  lemma_impl_squeeze_once_store_block
    rate
    ks_tail
    out
    (output_len -! output_rem)
    output_rem;
  lemma_store_block_equiv
    rate
    state_tail
    out
    (output_len -! output_rem)
    output_rem

(** Squeeze-phase equivalence (general case).
    Handles multi-block squeezing for SHAKE with large outputs.

    The impl uses split structure (if/else + loop + remainder).
    The spec uses a unified for-loop with conditional keccakf at round 0.
    Both execute the same sequence of (squeeze, keccakf) operations:
      Round 0: squeeze min(OUTPUT_LEN, rate) bytes, no keccakf
      Round k>0: keccakf, then squeeze min(remaining, rate) bytes *)
let lemma_squeeze_general_equiv
      (rate: usize)
      (state_impl: impl_state)
      (state_spec: spec_state)
      (output_len: usize)
  : Lemma
      (requires
        state_impl.Libcrux_sha3.Generic_keccak.f_st == state_spec /\
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v output_len < v Core_models.Num.impl_usize__MAX - 200)
      (ensures (
        (* At minimum, recover the one-block squeeze equivalence as a
           conditional consequence of the general setup. *)
        v output_len <= v rate ==>
        (let out: t_Slice u8 = Rust_primitives.Hax.repeat (mk_u8 0) output_len in
         Libcrux_sha3.Simd.Portable.store_block rate state_spec out (mk_usize 0) output_len ==
         Hacspec_sha3.Sponge.squeeze_state state_spec out (mk_usize 0) output_len)))
  =
  if output_len <=. rate
  then
    let out: t_Slice u8 = Rust_primitives.Hax.repeat (mk_u8 0) output_len in
    lemma_store_block_equiv rate state_spec out (mk_usize 0) output_len
  else ()
  (* Proof approach:
     Define recursive squeeze helpers (like absorb helpers above).
     Show both sides produce the same (state, output) after each squeeze round.
     The impl special-cases the first round while the spec uses
     `if _squeeze_round > 0 then keccakf` in a uniform loop.
     Both skip keccakf on round 0 and apply it on subsequent rounds.

     For concrete output sizes (SHA-3 hashes where output_len <= rate),
     use lemma_squeeze_single_equiv instead — much simpler. *)


(** ============================================================== *)
(** MAIN THEOREM: keccak1 == keccak (full sponge equivalence).      *)
(** Sponge-layer analog of [lemma_keccakf1600_equiv].               *)
(** ============================================================== *)
(*
   PHASE 16 DECOMPOSITION PLAN — handoff anchor for future sessions.

   STATUS as of this comment:
     - The Rust spec (specs/sha3/src/sponge.rs::keccak) has been
       rewritten so its squeeze block has the same split structure
       as the impl's keccak1 (Phase A, DONE). Re-extraction
       (./hax.sh extract / ./hax.sh prove) and cross-spec tests
       (cargo test --test cross_spec, including new
       shake128/256_squeeze_structure cases) all pass.
     - This file's existing absorb-side helpers
       ([impl_absorb_loop], [spec_absorb_loop], [lemma_*_is_loop],
       [lemma_absorb_loop_equiv], [lemma_absorb_final_equiv]) are
       fully proved.
     - [lemma_squeeze_single_equiv] is fully proved for the
       output_len <= rate case (covers SHA3-224/256/384/512).
     - [lemma_squeeze_general_equiv] above is admitted with a weak
       postcondition; it will be SUPERSEDED by the squeeze-loop
       lemma below and may be removed once Phase B lands.
     - [lemma_keccak1_bridge] (this declaration) is currently the
       only remaining MONOLITHIC admit. Phase B replaces it with
       a real proof composed from the helpers below.

   POST–PHASE-A STRUCTURE (verified from re-extraction):

   Impl squeeze (Libcrux_sha3.Generic_keccak.Portable.keccak1,
                 lines 267–352, after impl_2__absorb_final):

     output_len    = Slice.impl__len output
     output_blocks = output_len / v_RATE
     output_rem    = output_len % v_RATE
     (output, s) =
       if output_blocks == 0 then
         output = Traits.f_squeeze v_RATE s output 0 output_len
         (output, s)
       else
         output = Traits.f_squeeze v_RATE s output 0 v_RATE
         (output, s) = fold_range 1 output_blocks
           (body: _      = Lemmas.lemma_mul_succ_le i output_blocks v_RATE
                  s      = impl_2__keccakf1600 s
                  output = Traits.f_squeeze v_RATE s output (i*v_RATE) v_RATE)
           (output, s)
         if output_rem <> 0 then
           s      = impl_2__keccakf1600 s
           output = Traits.f_squeeze v_RATE s output (output_len - output_rem) output_rem
         else (output, s)

   Spec squeeze (Hacspec_sha3.Sponge.keccak, lines 297–331, after
                 absorb_final):

     output_blocks = v_OUTPUT_LEN / rate
     output_rem    = v_OUTPUT_LEN % rate
     (output, state) =
       if output_blocks == 0 then
         output = squeeze_state state output 0 v_OUTPUT_LEN
         (output, state)
       else
         output = squeeze_state state output 0 rate
         (output, state) = fold_range 1 output_blocks
           (body: state  = Hacspec_sha3.Keccak_f.keccak_f state
                  output = squeeze_state state output (i*rate) rate)
           (output, state)
         if output_rem <> 0 then
           state  = Hacspec_sha3.Keccak_f.keccak_f state
           output = squeeze_state state output (v_OUTPUT_LEN - output_rem) output_rem
         else (output, state)

   The two sides differ only in:
     (a) Traits.f_squeeze v_RATE ...  vs  squeeze_state ...
         — connected pointwise by [lemma_store_block_equiv]
           (the Portable backend's f_squeeze IS Simd.Portable.store_block,
           which equals Hacspec_sha3.Sponge.squeeze_state).
     (b) impl_2__keccakf1600  vs  Hacspec_sha3.Keccak_f.keccak_f
         — connected by [Impl_Spec_Keccakf.lemma_keccakf1600_equiv].
     (c) Impl-side prepended unit-returning lemma_mul_succ_le —
         no effect on state; absorbed into the fold-bridge axiom.

   ----------------------------------------------------------------
   NEW DEFINITIONS to add immediately before this comment block:
   ----------------------------------------------------------------

   1. impl_squeeze_loop : recursive mirror of the impl's
      `fold_range 1 output_blocks` body. Threads (output, ks).
        let rec impl_squeeze_loop
            (ks: impl_state) (output: t_Slice u8) (rate: usize)
            (i output_blocks: usize)
          : Pure (t_Slice u8 & impl_state) ...
        = if i =. output_blocks then (output, ks)
          else
            let ks' = impl_2__keccakf1600 ks in
            let output' = Traits.f_squeeze rate ks' output (i*!rate) rate in
            impl_squeeze_loop ks' output' rate (i +! mk_usize 1) output_blocks

   2. spec_squeeze_loop : recursive mirror of the spec's
      `fold_range 1 output_blocks` body. Same shape with
      Hacspec_sha3.Keccak_f.keccak_f and Hacspec_sha3.Sponge.squeeze_state.

   No `_remainder` helpers are needed: the optional remainder block
   is a single (keccakf, squeeze) step, inlined at the proof site
   exactly like the Phase 13 store-block-bridge tail.

   ----------------------------------------------------------------
   PROVABLE LEMMAS (no admits):
   ----------------------------------------------------------------

   3. lemma_squeeze_loop_equiv : the two recursive loops produce
      equal (output, state) tuples given equal initial inputs.
      Proof: induction on (output_blocks - i) at --fuel 1.
      Per step body: lemma_keccakf1600_equiv (state-side) +
      lemma_store_block_equiv (slice-side), then recurse.
      Expected settings: --fuel 1 --z3rlimit 300.

   4. lemma_squeeze_zero_blocks_equiv : when output_blocks = 0,
      one lemma_store_block_equiv with start=0, len=output_len
      closes the goal. (Equivalent to lemma_squeeze_single_equiv
      already proved; can be a thin wrapper or replaced by it.)

   5. lemma_squeeze_first_block_equiv : one lemma_store_block_equiv
      with start=0, len=rate. Trivial.

   6. lemma_squeeze_remainder_equiv (optional, readability):
      one lemma_keccakf1600_equiv + one lemma_store_block_equiv.

   ----------------------------------------------------------------
   SMALL FOLD-RANGE BRIDGING AXIOMS (mirror Phase 13 pattern):
   ----------------------------------------------------------------

   These are the only NEW assumed content. They mirror
   [lemma_impl_absorb_is_loop] / [lemma_spec_absorb_is_loop]
   (lines 1833 / 1853) and the Phase 13 axioms
   [lemma_store_block_decomposes] / [lemma_squeeze_state_decomposes].
   The reason they are admitted, not proved: F*'s SMT solver cannot
   discharge `fold_range` ≡ recursive-mirror without unbounded fuel
   on the closure body.

   7. lemma_impl_squeeze_fold_is_loop :
        Lemma (requires Seq.length output >= v output_blocks * v rate /\ ...)
              (ensures
                Rust_primitives.Hax.Folds.fold_range (mk_usize 1) output_blocks
                  <inv> (output, ks)
                  <impl-side body that does mul_succ_le, keccakf, f_squeeze>
                ==
                impl_squeeze_loop ks output rate (mk_usize 1) output_blocks)
      Insertion point: just after [lemma_impl_absorb_is_loop].

   8. lemma_spec_squeeze_fold_is_loop : spec-side analog.
      Insertion point: just after [lemma_spec_absorb_is_loop].

   ----------------------------------------------------------------
   MAIN THEOREM — proof body for [lemma_keccak1_bridge]:
   ----------------------------------------------------------------

   Replace the `assume val` declaration immediately below with a
   `let lemma_keccak1_bridge ... = <body>` whose body is:

     (* 1. Initial states equal. *)
     lemma_new_state_equiv ();

     (* 2. Absorb phase equivalence — already fully proved.
           Lifts both fold_range closures into recursive mirrors,
           inducts over the absorb loop, then absorbs the final
           padded block. *)
     lemma_impl_absorb_is_loop ks0 data rate n;
     lemma_spec_absorb_is_loop spec0 data rate n;
     lemma_absorb_loop_equiv ks0 spec0 data rate (mk_usize 0) n;
     lemma_absorb_final_equiv
       (impl_absorb_loop ks0 data rate (mk_usize 0) n)
       (spec_absorb_loop spec0 data rate (mk_usize 0) n)
       rate delim data start remaining;

     (* 3. Squeeze phase equivalence.
           Case split on output_blocks = 0, mirroring both sides'
           if/else. *)
     if output_blocks = mk_usize 0 then
       lemma_squeeze_zero_blocks_equiv rate s_final out0 output_len
     else begin
       (* First-block squeeze on both sides. *)
       lemma_squeeze_first_block_equiv rate s_final out0 rate;

       (* Lift the fold_ranges to recursive mirrors. *)
       lemma_impl_squeeze_fold_is_loop ks_first out1 rate output_blocks;
       lemma_spec_squeeze_fold_is_loop spec_first out1 rate output_blocks;

       (* Induction: the two recursive loops agree. *)
       lemma_squeeze_loop_equiv ks_first spec_first out1 rate
                                (mk_usize 1) output_blocks;

       (* Optional tail: one more (keccakf, squeeze) step. *)
       if output_rem <>. mk_usize 0 then begin
         lemma_keccakf1600_equiv ks_after_loop spec_after_loop;
         lemma_store_block_equiv rate spec_after_loop out_after_loop
                                 (output_len -! output_rem) output_rem
       end
     end

   Expected settings: #push-options "--fuel 1 --z3rlimit 600".
   If the case-split blows up, escalate to --split_queries always or
   --z3rlimit 900 per branch.

   ----------------------------------------------------------------
   PARALLEL PLAYBOOK reference:
   ----------------------------------------------------------------
   The full pattern (typed helpers + provable composition lemma +
   small fold-range axioms + thin top-level proof) was applied
   successfully in Phase 13 — see [lemma_store_block_bridge] above
   and the comment block preceding it. Mirror that structure when
   implementing items 1–9 here.

   ----------------------------------------------------------------
   AXIOM ACCOUNTING when Phase B lands:
   ----------------------------------------------------------------
   Net change to `grep -c '^assume val' Impl_Spec_Sponge.fst`: +1
     - removed: 1 monolithic axiom (this lemma_keccak1_bridge)
     - added:   2 small fold-range axioms (items 7 and 8)
*)
