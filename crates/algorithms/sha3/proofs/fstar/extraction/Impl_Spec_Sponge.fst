module Impl_Spec_Sponge

(* ================================================================
   Sponge-layer equivalence between the libcrux SHA-3 implementation
   and the hacspec specification.

   Builds on Impl_Spec_Keccakf.lemma_keccakf1600_equiv:
     keccakf1600(ks).f_st == keccak_f(ks.f_st)

   This file extends the proof to the full sponge construction
   (absorb, pad, squeeze) and top-level hash functions.

   Function correspondence (1:1 after spec restructuring):
     IMPL                                    SPEC
     ----                                    ----
     load_block                         <->  xor_block_into_state
     load_last                          <->  pad_last_block + load_block
     store_block                        <->  squeeze_state
     absorb_block (impl_2__absorb_block)<->  absorb_block
     absorb_final                       <->  absorb_final
     keccak1                            <->  keccak
     Portable.sha256                    <->  sha3_256_
     Libcrux_sha3.sha256               <->  sha3_256_
     (and similarly for sha224, sha384, sha512, shake128, shake256)

   Structure:
     Phase 9:  Rate/delimiter constant matching
     Phase 10: Lane indexing equivalence
     Phase 11: load_block == xor_block_into_state
     Phase 12: load_last == pad_last_block + xor_block_into_state
     Phase 13: store_block == squeeze_state
     Phase 14: Single absorb step: impl absorb_block == spec absorb_block
     Phase 15: Absorb loop equivalence (recursive helpers + induction)
     Phase 16: Full sponge equivalence (keccak1 == keccak)
     Phase 17: Top-level hash functions

   Remaining structural mismatches (proof cost to absorb):
     C2: load_block is two-phase (read-all then XOR-all) vs
         xor_block_into_state one-phase (read-and-XOR).
         Provable via lane_index injectivity.
     Squeeze: impl uses split structure (if/else + loop + remainder),
         spec uses unified for-loop with conditional keccakf at round 0.
         Both execute the same sequence of (squeeze, keccakf) operations.
   ================================================================ *)

#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"

open FStar.Mul
open Core_models

(* Bring typeclass instances into scope so that
   KeccakItem u64 1 resolves to the portable impl. *)
let _ =
  let open Libcrux_sha3.Traits in
  let open Libcrux_sha3.Simd.Portable in
  ()

(* Shorthand types *)
let impl_state = Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64
let spec_state = t_Array u64 (mk_usize 25)


(* ================================================================
   Phase 9: Rate and Delimiter Constant Equivalence

   The impl (Libcrux_sha3.Portable) and spec (Hacspec_sha3.Sha3)
   use identical rate and delimiter values for each hash variant.

   Proof: definitional — both are the same integer literals.
   ================================================================ *)

let lemma_sha3_224_rate  (_:unit) : Lemma (mk_usize 144 == Hacspec_sha3.Sha3.v_SHA3_224_RATE)  = ()
let lemma_sha3_256_rate  (_:unit) : Lemma (mk_usize 136 == Hacspec_sha3.Sha3.v_SHA3_256_RATE)  = ()
let lemma_sha3_384_rate  (_:unit) : Lemma (mk_usize 104 == Hacspec_sha3.Sha3.v_SHA3_384_RATE)  = ()
let lemma_sha3_512_rate  (_:unit) : Lemma (mk_usize 72  == Hacspec_sha3.Sha3.v_SHA3_512_RATE)  = ()
let lemma_shake128_rate  (_:unit) : Lemma (mk_usize 168 == Hacspec_sha3.Sha3.v_SHAKE128_RATE)  = ()
let lemma_shake256_rate  (_:unit) : Lemma (mk_usize 136 == Hacspec_sha3.Sha3.v_SHAKE256_RATE)  = ()
let lemma_sha3_delim     (_:unit) : Lemma (mk_u8 6  == Hacspec_sha3.Sha3.v_SHA3_DELIM)         = ()
let lemma_shake_delim    (_:unit) : Lemma (mk_u8 31 == Hacspec_sha3.Sha3.v_SHAKE_DELIM)        = ()


(* ================================================================
   Phase 10: Lane Index Equivalence

   The spec uses:
     lane_index(l) = 5*(l%5) + l/5

   The impl's load_block/store_block use:
     set_ij(1, state, i/5, i%5)  which writes to  state[5*(i%5) + i/5]
     get_ij(1, state, i/5, i%5)  which reads       state[5*(i%5) + i/5]

   Both map lane l to flat index 5*(l%5) + l/5.  This is the same
   (x,y) transposition from Phase 2 of Impl_Spec_Keccakf, just
   expressed in terms of lane number: lane l has (y,x) = (l/5, l%5).

   Proof: definitional — lane_index is defined as 5*(l%5) + l/5.
   ================================================================ *)

let lemma_lane_index_is_impl_index (i: usize)
  : Lemma (requires v i < 25)
          (ensures  Hacspec_sha3.Sponge.lane_index i ==
                    (mk_usize 5 *! (i %! mk_usize 5 <: usize) <: usize) +!
                    (i /! mk_usize 5 <: usize))
  = ()


(* ================================================================
   Phase 11: load_block == xor_block_into_state

   Impl: Libcrux_sha3.Simd.Portable.load_block(RATE, state, blocks, start)
     Loop 1 (i in 0..RATE/8):
       state_flat[i] = from_le_bytes(try_into(blocks[start+8*i .. start+8*i+8]))
     Loop 2 (i in 0..RATE/8):
       state[lane_index(i)] ^= state_flat[i]
       (via set_ij(1, state, i/5, i%5))

   Spec: Hacspec_sha3.Sponge.xor_block_into_state(state, block, rate)
     Single loop (i in 0..rate/8):
       lane_val = from_le_bytes(try_into(block[8*i..8*i+8]))
       state[lane_index(i)] ^= lane_val

   Both now use try_into for byte reading (B2 fix applied).
   The only remaining mismatch is two-phase vs single-phase (C2).

   Proof sketch:
   1. The impl's two-loop approach (read-all-then-XOR-all) equals the
      spec's single-loop approach (read-and-XOR) because:
      - All lane_index(i) values are distinct for 0 <= i < 25
      - Each state element is modified at most once
      - So the order of reads/writes doesn't matter
   2. With block = blocks[start..start+rate], both read the same bytes.
   3. Per-element equality: for each j < 25,
      if j = lane_index(i) for some i < RATE/8:
        result[j] = state[j] ^ from_le_bytes(bytes_at_lane_i)
      else: result[j] = state[j]
   4. Lift to array equality via forall_intro + eq_intro.

   Difficulty: HARD. Two fold_range loops vs one.
   May need --fuel for loop unrolling, or recursive bridge + induction.
   ================================================================ *)

#push-options "--z3rlimit 200"
let lemma_load_block_equiv
      (rate: usize)
      (state: spec_state)
      (data: t_Slice u8)
      (start: usize)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v start + v rate <= Seq.length data)
      (ensures
        Libcrux_sha3.Simd.Portable.load_block rate state data start ==
        Hacspec_sha3.Sponge.xor_block_into_state state
          (data.[ { Core_models.Ops.Range.f_start = start;
                     Core_models.Ops.Range.f_end = start +! rate } <:
                   Core_models.Ops.Range.t_Range usize ])
          rate)
  = admit ()
  (* Proof approach:
     - Define per-element function f(j) = if exists i < rate/8 s.t. lane_index(i) = j
                                          then state[j] ^ from_le_bytes(...)
                                          else state[j]
     - Show both sides compute f(j) at each index j
     - Use eq_intro *)
#pop-options


(* ================================================================
   Phase 12: load_last == pad_last_block + load_block

   Impl: Libcrux_sha3.Simd.Portable.load_last(RATE, DELIM, state, blocks, start, len)
     1. buffer = Array.repeat 0 RATE          (RATE bytes, all zero)
     2. buffer[0..len] = blocks[start..start+len]
     3. buffer[len] = DELIM
     4. buffer[RATE-1] |= 0x80
     5. load_block(RATE, state, buffer, 0)

   Spec: Hacspec_sha3.Sponge.pad_last_block(message, msg_offset, remaining, rate, delim)
     1. buffer = Array.repeat 0 200           (200 bytes, all zero)
     2. buffer[0..remaining] = message[msg_offset..msg_offset+remaining]
     3. buffer[remaining] = delim
     4. buffer[rate-1] |= 0x80
     Returns buffer (t_Array u8 200)

   Then: absorb_block(state, buffer, rate) = xor_block_into_state(state, buffer, rate) + keccak_f

   Proof sketch:
   1. Show buffer[0..RATE] is identical in both (impl uses RATE-byte
      buffer, spec uses 200-byte buffer, but bytes 0..RATE-1 match):
      - Positions 0..len-1: same message bytes (copy_from_slice)
      - Position len: both write DELIM
      - Positions len+1..RATE-2: both zero
      - Position RATE-1: both 0x00 | 0x80 = 0x80 (or DELIM | 0x80 if len = RATE-1)
   2. xor_block_into_state only reads bytes 0..rate-1, so the extra
      zeros in the 200-byte buffer don't matter.
   3. Apply lemma_load_block_equiv with start=0.

   Difficulty: MEDIUM. Buffer content equality is straightforward.
   ================================================================ *)

#push-options "--z3rlimit 200"
let lemma_load_last_equiv
      (rate: usize)
      (delim: u8)
      (state: spec_state)
      (data: t_Slice u8)
      (start len: usize)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v len < v rate /\
        v start + v len <= Seq.length data)
      (ensures (
        let impl_result = Libcrux_sha3.Simd.Portable.load_last rate delim state data start len in
        let padded = Hacspec_sha3.Sponge.pad_last_block data start len rate delim in
        impl_result ==
          Hacspec_sha3.Sponge.xor_block_into_state state (padded <: t_Slice u8) rate))
  = admit ()
  (* Proof approach:
     1. Show the padding bytes match in positions 0..RATE-1
     2. Use lemma_load_block_equiv to bridge load_block -> xor_block_into_state
     3. Show xor_block_into_state depends only on first rate bytes *)
#pop-options

(** Stronger form linking load_last to spec's absorb_final path. *)
#push-options "--z3rlimit 200"
let lemma_load_last_as_absorb
      (rate: usize)
      (delim: u8)
      (state: spec_state)
      (message: t_Slice u8)
      (num_full_blocks: usize)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v num_full_blocks == Seq.length message / v rate /\
        v num_full_blocks * v rate <= Seq.length message)
      (ensures (
        let remaining = mk_usize (Seq.length message - v num_full_blocks * v rate) in
        let start = num_full_blocks *! rate in
        let impl_result =
          Libcrux_sha3.Simd.Portable.load_last rate delim state message start remaining in
        let padded = Hacspec_sha3.Sponge.pad_last_block message start remaining rate delim in
        impl_result ==
          Hacspec_sha3.Sponge.xor_block_into_state state (padded <: t_Slice u8) rate))
  = admit ()
#pop-options


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

#push-options "--z3rlimit 200"
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
  = admit ()
  (* Proof approach:
     1. Show get_ij(1, state, i/5, i%5) == state[lane_index(i)]
        by Phase 10 + Phase 2 of Impl_Spec_Keccakf.
     2. Both use copy_from_slice — same idiom after spec restructuring.
     3. Per-position: both write the same byte at each output position.
     4. Seq.lemma_eq_intro for overall equality. *)
#pop-options


(* ================================================================
   Phase 14: Single Absorb Step Equivalence

   Impl: absorb_block(1, RATE, ks, [data], start)
     = let ks' = { ks with f_st = load_block(RATE, ks.f_st, data, start) }
       keccakf1600(ks')

   Spec: Hacspec_sha3.Sponge.absorb_block(state, block, rate)
     = let state' = xor_block_into_state(state, block, rate)
       keccak_f(state')

   Both are named functions with the same structure.

   Proof: compose Phase 11 (load_block == xor_block_into_state) with
   Impl_Spec_Keccakf.lemma_keccakf1600_equiv.
   ================================================================ *)

let lemma_absorb_block_equiv
      (ks: impl_state)
      (state: spec_state)
      (rate: usize)
      (data: t_Slice u8)
      (start: usize)
  : Lemma
      (requires
        ks.Libcrux_sha3.Generic_keccak.f_st == state /\
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v start + v rate <= Seq.length data /\
        Libcrux_sha3.Proof_utils.slices_same_len (mk_usize 1)
          (let list = [data] in
           FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
           Rust_primitives.Hax.array_of_list 1 list))
      (ensures (
        let ks' = Libcrux_sha3.Generic_keccak.impl_2__absorb_block (mk_usize 1)
                    #u64 rate ks
                    (let list = [data] in
                     FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                     Rust_primitives.Hax.array_of_list 1 list)
                    start in
        let block = data.[ { Core_models.Ops.Range.f_start = start;
                              Core_models.Ops.Range.f_end = start +! rate } <:
                            Core_models.Ops.Range.t_Range usize ] in
        ks'.Libcrux_sha3.Generic_keccak.f_st ==
        Hacspec_sha3.Sponge.absorb_block state block rate))
  = admit ()
  (* Proof:
     1. Unfold impl absorb_block: f_load_block then keccakf1600
     2. f_load_block resolves to load_block on ks.f_st
     3. lemma_load_block_equiv: load_block(rate, state, data, start)
                              == xor_block_into_state(state, data[start..start+rate], rate)
     4. Impl_Spec_Keccakf.lemma_keccakf1600_equiv:
        keccakf1600({f_st = loaded}).f_st == keccak_f(loaded)
     5. spec absorb_block(state, block, rate)
        = keccak_f(xor_block_into_state(state, block, rate))
        by definition
     6. Combine: result.f_st == spec absorb_block(state, block, rate) *)


(** Absorb-final step: compose load_last with keccakf1600 to match
    spec's absorb_final = pad_last_block + absorb_block. *)
let lemma_absorb_final_equiv
      (ks: impl_state)
      (state: spec_state)
      (rate: usize)
      (delim: u8)
      (data: t_Slice u8)
      (start remaining: usize)
  : Lemma
      (requires
        ks.Libcrux_sha3.Generic_keccak.f_st == state /\
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v remaining < v rate /\
        v start + v remaining <= Seq.length data /\
        v start <= Seq.length data /\
        Libcrux_sha3.Proof_utils.slices_same_len (mk_usize 1)
          (let list = [data] in
           FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
           Rust_primitives.Hax.array_of_list 1 list))
      (ensures (
        let ks' = Libcrux_sha3.Generic_keccak.impl_2__absorb_final (mk_usize 1)
                    #u64 rate delim ks
                    (let list = [data] in
                     FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                     Rust_primitives.Hax.array_of_list 1 list)
                    start remaining in
        ks'.Libcrux_sha3.Generic_keccak.f_st ==
        Hacspec_sha3.Sponge.absorb_final state data start remaining rate delim))
  = admit ()
  (* Proof:
     1. Unfold impl absorb_final: f_load_last then keccakf1600
     2. lemma_load_last_equiv: load_last produces same state as
        xor_block_into_state(state, pad_last_block(...), rate)
     3. Impl_Spec_Keccakf.lemma_keccakf1600_equiv for the keccakf step
     4. Spec absorb_final(state, msg, off, rem, rate, delim)
        = absorb_block(state, pad_last_block(msg, off, rem, rate, delim), rate)
        = keccak_f(xor_block_into_state(state, padded, rate))
        by definitions of absorb_final and absorb_block *)


(* ================================================================
   Phase 15: Absorb Loop Equivalence

   Strategy: define recursive helpers that mirror the fold_range loops
   on both sides, prove a bridge (fold_range == recursive helper) at
   high fuel, then prove equivalence by induction at fuel 1.

   This follows the same pattern as impl_rounds/spec_rounds in
   Impl_Spec_Keccakf.fst (Phase 8).
   ================================================================ *)

(* Recursive helper mirroring the impl's absorb loop *)
let rec impl_absorb_loop
      (ks: impl_state)
      (data: t_Slice u8)
      (rate: usize)
      (i n: usize)
  : Pure impl_state
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v i <= v n /\
        v n * v rate <= Seq.length data)
      (ensures fun _ -> True)
      (decreases (v n - v i))
  = if i =. n then ks
    else
      let start = i *! rate in
      let ks' = Libcrux_sha3.Generic_keccak.impl_2__absorb_block (mk_usize 1) #u64 rate
                  ks
                  (let list = [data] in
                   FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                   Rust_primitives.Hax.array_of_list 1 list)
                  start in
      impl_absorb_loop ks' data rate (i +! mk_usize 1) n

(* Recursive helper mirroring the spec's absorb loop.
   Now calls the named Hacspec_sha3.Sponge.absorb_block. *)
let rec spec_absorb_loop
      (state: spec_state)
      (message: t_Slice u8)
      (rate: usize)
      (i n: usize)
  : Pure spec_state
      (requires
        v rate > 0 /\ v rate <= 200 /\ v rate % 8 == 0 /\
        v i <= v n /\
        v n * v rate <= Seq.length message)
      (ensures fun _ -> True)
      (decreases (v n - v i))
  = if i =. n then state
    else
      let offset = i *! rate in
      let block = message.[ { Core_models.Ops.Range.f_start = offset;
                                Core_models.Ops.Range.f_end = offset +! rate } <:
                              Core_models.Ops.Range.t_Range usize ] in
      let state' = Hacspec_sha3.Sponge.absorb_block state block rate in
      spec_absorb_loop state' message rate (i +! mk_usize 1) n

(** Bridge: the impl's fold_range in keccak1 == impl_absorb_loop.
    Needs high fuel to unroll fold_range. *)
(* #push-options "--fuel 26 --z3rlimit 300"
   For concrete rates this might not work with fuel alone if the
   rate is symbolic. May need the fold_range_step peeling lemma. *)
let lemma_impl_absorb_is_loop
      (ks: impl_state)
      (data: t_Slice u8)
      (rate: usize)
      (n: usize)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v n * v rate <= Seq.length data)
      (ensures True (* fold_range 0 n ... == impl_absorb_loop ks data rate 0 n *))
  = admit ()
  (* Proof: Since n is symbolic (depends on input length), high fuel won't
     work. Use lemma_fold_range_step peeling: show fold_range(0,n,...) ==
     fold_range(1,n,...,f(init,0)). Then by induction. *)

(** Bridge: the spec's fold_range in keccak == spec_absorb_loop.
    The spec's absorb loop body now calls absorb_block directly,
    which matches spec_absorb_loop exactly. *)
let lemma_spec_absorb_is_loop
      (state: spec_state)
      (message: t_Slice u8)
      (rate: usize)
      (n: usize)
  : Lemma
      (requires
        v rate > 0 /\ v rate <= 200 /\ v rate % 8 == 0 /\
        v n * v rate <= Seq.length message)
      (ensures True (* fold_range 0 n ... == spec_absorb_loop state message rate 0 n *))
  = admit ()

(** Inductive equivalence: impl_absorb_loop.f_st == spec_absorb_loop.
    Analogous to lemma_rounds_equiv in Impl_Spec_Keccakf. *)
#push-options "--fuel 1 --z3rlimit 200"
let rec lemma_absorb_loop_equiv
      (ks: impl_state)
      (state: spec_state)
      (data: t_Slice u8)
      (rate: usize)
      (i n: usize)
  : Lemma
      (requires
        ks.Libcrux_sha3.Generic_keccak.f_st == state /\
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v i <= v n /\
        v n * v rate <= Seq.length data)
      (ensures
        (impl_absorb_loop ks data rate i n).Libcrux_sha3.Generic_keccak.f_st ==
        spec_absorb_loop state data rate i n)
      (decreases (v n - v i))
  = admit ()
  (* Proof:
     if i = n: both return the input state. QED.
     else:
       1. lemma_absorb_block_equiv ks state rate data (i*rate):
          impl absorb_block result.f_st == spec absorb_block(state, block, rate)
       2. Recursive call: lemma_absorb_loop_equiv ks' state' data rate (i+1) n
       3. By induction hypothesis, the remaining iterations match. *)
#pop-options


(* ================================================================
   Phase 16: Full Sponge Equivalence

   Impl: keccak1(RATE, DELIM, input, output)
     1. s = new()                                    -- zero state
     2. Absorb loop: fold_range 0 input_blocks       -- absorb full blocks
        Each iteration calls impl absorb_block
     3. absorb_final(s, [input], start, rem)          -- pad + absorb last
     4. Squeeze: first block, then loop + remainder   -- extract output
        SPLIT structure: if/else + loop + conditional remainder

   Spec: keccak(OUTPUT_LEN, rate, delim, message)
     1. state = repeat 0 25                           -- zero state
     2. Absorb loop: fold_range 0 num_full_blocks     -- absorb full blocks
        Each iteration calls spec absorb_block
     3. absorb_final(state, msg, offset, rem, rate, delim) -- pad + absorb
     4. Squeeze: unified for-loop with conditional keccakf at round 0

   After restructuring, both sides have 1:1 function correspondence
   in the absorb phase. The squeeze phase still differs structurally
   but both execute the same (squeeze, keccakf) sequence.
   ================================================================ *)

(** New state equivalence: both sides start from all-zero state *)
let lemma_new_state_equiv (_: unit)
  : Lemma (
      (Libcrux_sha3.Generic_keccak.impl_2__new (mk_usize 1) #u64 ())
        .Libcrux_sha3.Generic_keccak.f_st ==
      Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 25))
  = admit ()
  (* Proof: impl_2__new creates { f_st = repeat (f_zero()) 25 }.
     f_zero() for u64 = mk_u64 0. So f_st = repeat (mk_u64 0) 25.
     Should be definitional, possibly needs unfolding f_zero. *)

(** Absorb-phase equivalence: after all full blocks + final block,
    the impl and spec states match. *)
let lemma_absorb_phase_equiv
      (rate: usize)
      (delim: u8)
      (data: t_Slice u8)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        Seq.length data <= v (cast Core_models.Num.impl_u32__MAX <: usize))
      (ensures (
        let n = Seq.length data / v rate in
        let _rem = Seq.length data % v rate in
        (* After absorbing all blocks:
           impl_state_after_absorb.f_st == spec_state_after_absorb *)
        True))
  = admit ()
  (* Proof:
     1. lemma_new_state_equiv: starting states match
     2. lemma_impl_absorb_is_loop + lemma_spec_absorb_is_loop: bridge fold_range
     3. lemma_absorb_loop_equiv: absorb loops produce equal states
     4. lemma_absorb_final_equiv: final block produces equal states *)

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
        (* When output_len <= rate:
           store_block(rate, state, impl_out, 0, output_len) ==
           squeeze_state(state, spec_out, 0, output_len)
           (given both output buffers have the same length and
            are both zero-filled) *)
        True))
  = admit ()
  (* Proof: direct application of lemma_store_block_equiv *)

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
        (* The impl's squeeze sequence (first block + loop + remainder)
           produces the same output bytes as the spec's unified squeeze loop.
           Both start from the same state and apply keccakf between blocks. *)
        True))
  = admit ()
  (* Proof approach:
     Define recursive squeeze helpers (like absorb helpers above).
     Show both sides produce the same (state, output) after each squeeze round.
     The impl special-cases the first round while the spec uses
     `if _squeeze_round > 0 then keccakf` in a uniform loop.
     Both skip keccakf on round 0 and apply it on subsequent rounds.

     For concrete output sizes (SHA-3 hashes where output_len <= rate),
     use lemma_squeeze_single_equiv instead — much simpler. *)


(** MAIN THEOREM: keccak1 == keccak (full sponge equivalence).
    This is the sponge-layer analog of lemma_keccakf1600_equiv. *)
let lemma_keccak1_equiv
      (rate: usize)
      (delim: u8)
      (output_len: usize)
      (data: t_Slice u8)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v output_len < v Core_models.Num.impl_usize__MAX - 200 /\
        Seq.length data <= v (cast Core_models.Num.impl_u32__MAX <: usize))
      (ensures (
        let impl_out : t_Slice u8 = Rust_primitives.Hax.repeat (mk_u8 0) output_len in
        let impl_result = Libcrux_sha3.Generic_keccak.Portable.keccak1
                            rate delim data impl_out in
        let spec_result = Hacspec_sha3.Sponge.keccak output_len rate delim data in
        (* The impl's output slice equals the spec's output array *)
        impl_result == (spec_result <: t_Slice u8)))
  = admit ()
  (* Proof:
     1. lemma_new_state_equiv: initial states match
     2. lemma_absorb_phase_equiv: states match after absorb
     3. lemma_squeeze_general_equiv: outputs match after squeeze
     4. Both output buffers start as zero-filled, same length *)


(* ================================================================
   Phase 17: Top-Level Hash Function Equivalence

   Each impl function is a thin wrapper:
     Libcrux_sha3.sha256(data)
       = let out = repeat 0 32
         sha256_ema(out, data)
       = let out = repeat 0 32
         Portable.sha256(out, data)
       = let out = repeat 0 32
         keccak1(136, 6, data, out)

   Each spec function is a thin wrapper:
     Hacspec_sha3.Sha3.sha3_256_(data)
       = keccak(32, 136, 6, data)

   So each top-level equivalence follows directly from keccak1 == keccak
   (Phase 16) plus rate/delimiter matching (Phase 9).
   ================================================================ *)

let lemma_sha256_equiv (data: t_Slice u8)
  : Lemma
      (requires
        Seq.length data <= v (cast Core_models.Num.impl_u32__MAX <: usize))
      (ensures
        Libcrux_sha3.sha256 data ==
        (Hacspec_sha3.Sha3.sha3_256_ data <: t_Slice u8))
  = admit ()
  (* Proof:
     1. Unfold sha256 -> sha256_ema -> Portable.sha256 -> keccak1(136, 6, data, zeros_32)
     2. Unfold sha3_256_ -> keccak(32, 136, 6, data)
     3. Apply lemma_keccak1_equiv with rate=136, delim=6, output_len=32
     4. lemma_sha3_256_rate, lemma_sha3_delim for constant matching *)

let lemma_sha224_equiv (data: t_Slice u8)
  : Lemma
      (requires
        Seq.length data <= v (cast Core_models.Num.impl_u32__MAX <: usize))
      (ensures
        Libcrux_sha3.sha224 data ==
        (Hacspec_sha3.Sha3.sha3_224_ data <: t_Slice u8))
  = admit ()

let lemma_sha384_equiv (data: t_Slice u8)
  : Lemma
      (requires
        Seq.length data <= v (cast Core_models.Num.impl_u32__MAX <: usize))
      (ensures
        Libcrux_sha3.sha384 data ==
        (Hacspec_sha3.Sha3.sha3_384_ data <: t_Slice u8))
  = admit ()

let lemma_sha512_equiv (data: t_Slice u8)
  : Lemma
      (requires
        Seq.length data <= v (cast Core_models.Num.impl_u32__MAX <: usize))
      (ensures
        Libcrux_sha3.sha512 data ==
        (Hacspec_sha3.Sha3.sha3_512_ data <: t_Slice u8))
  = admit ()

let lemma_shake128_equiv (v_BYTES: usize) (data: t_Slice u8)
  : Lemma
      (requires
        v v_BYTES < v Core_models.Num.impl_usize__MAX - 200)
      (ensures
        Libcrux_sha3.shake128 v_BYTES data ==
        (Hacspec_sha3.Sha3.shake128 v_BYTES data <: t_Slice u8))
  = admit ()

let lemma_shake256_equiv (v_BYTES: usize) (data: t_Slice u8)
  : Lemma
      (requires
        v v_BYTES < v Core_models.Num.impl_usize__MAX - 200)
      (ensures
        Libcrux_sha3.shake256 v_BYTES data ==
        (Hacspec_sha3.Sha3.shake256 v_BYTES data <: t_Slice u8))
  = admit ()
