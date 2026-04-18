module EquivImplSpec.Sponge.Portable.Steps

(* ================================================================
   Per-step equivalences for the Portable (N=1, v_T=u64) backend.

   Four step lemmas connecting single-block impl operations to the
   scalar Hacspec spec:

   - [lemma_absorb_block_portable] : impl_2__absorb_block ≡ spec absorb_block
   - [lemma_absorb_last_portable]  : impl_2__absorb_final ≡ spec absorb_final
   - [lemma_squeeze_block_portable]: keccakf1600 ; f_squeeze (len=rate) ≡
                                     keccak_f ; squeeze_state (len=rate)
   - [lemma_squeeze_last_portable] : keccakf1600 ; f_squeeze (len<rate) ≡
                                     keccak_f ; squeeze_state (len<rate)

   Absorb-side proofs ([lemma_absorb_block_portable],
   [lemma_absorb_last_portable]) use the pointwise [load_block] ensures
   (proved on the Rust side via hax_lib::ensures) together with the
   [createi_lemma] SMT pattern on the [createi]-form spec
   [xor_block_into_state]. No admit is reached on this side.

   Squeeze-side proofs still compose the admitted [portable_sc_store_block]
   at lane l=0 with the N=1 extract-lane identity and
   [lemma_keccakf1600_portable].
   ================================================================ *)

#set-options "--fuel 1 --ifuel 1 --z3rlimit 150"

open FStar.Mul
open Core_models

module G  = EquivImplSpec.Keccakf.Generic
module KP = EquivImplSpec.Keccakf.Portable
module SP = EquivImplSpec.Sponge.Portable

(* Bring Portable typeclass instances into scope so
   t_KeccakItem u64 1 / t_Absorb / t_Squeeze resolve. *)
let _ =
  let open Libcrux_sha3.Traits in
  let open Libcrux_sha3.Simd.Portable in
  ()


(* ================================================================
   Slice-of-slice byte equality helper.

   For a message [blocks], start offset [start], block size [rate],
   and lane index [k < rate/8]:
     (blocks[start..start+rate])[8k..8k+8] == blocks[start+8k..start+8k+8]

   Used to connect the pointwise ensures of [load_block] (which reads
   [blocks[start+8k..start+8k+8]]) to the [createi]-form spec
   [xor_block_into_state] (which reads [block[8k..8k+8]]).
   ================================================================ *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"
let lemma_subslice_bytes_eq
      (blocks: t_Slice u8) (start: usize) (rate: usize) (k: usize)
  : Lemma
      (requires
        v start + v rate <= Seq.length #u8 blocks /\
        v rate % 8 == 0 /\
        v k < v rate / 8 /\
        v start + 8 * v k + 8 <= Seq.length #u8 blocks)
      (ensures (
        let block : t_Slice u8 =
          blocks.[ { Core_models.Ops.Range.f_start = start;
                     Core_models.Ops.Range.f_end   = start +! rate } <:
                   Core_models.Ops.Range.t_Range usize ] in
        let lhs : t_Slice u8 =
          block.[ { Core_models.Ops.Range.f_start = mk_usize 8 *! k;
                    Core_models.Ops.Range.f_end   =
                      (mk_usize 8 *! k <: usize) +! mk_usize 8 } <:
                  Core_models.Ops.Range.t_Range usize ] in
        let rhs : t_Slice u8 =
          blocks.[ { Core_models.Ops.Range.f_start =
                       start +! (mk_usize 8 *! k <: usize);
                     Core_models.Ops.Range.f_end   =
                       (start +! (mk_usize 8 *! k <: usize) <: usize)
                       +! mk_usize 8 } <:
                   Core_models.Ops.Range.t_Range usize ] in
        lhs == rhs))
  = let block : t_Slice u8 =
      blocks.[ { Core_models.Ops.Range.f_start = start;
                 Core_models.Ops.Range.f_end   = start +! rate } <:
               Core_models.Ops.Range.t_Range usize ] in
    let lhs : t_Slice u8 =
      block.[ { Core_models.Ops.Range.f_start = mk_usize 8 *! k;
                Core_models.Ops.Range.f_end   =
                  (mk_usize 8 *! k <: usize) +! mk_usize 8 } <:
              Core_models.Ops.Range.t_Range usize ] in
    let rhs : t_Slice u8 =
      blocks.[ { Core_models.Ops.Range.f_start =
                   start +! (mk_usize 8 *! k <: usize);
                 Core_models.Ops.Range.f_end   =
                   (start +! (mk_usize 8 *! k <: usize) <: usize)
                   +! mk_usize 8 } <:
               Core_models.Ops.Range.t_Range usize ] in
    let aux (m: nat{m < 8}) : Lemma (Seq.index lhs m == Seq.index rhs m) = () in
    Classical.forall_intro aux;
    assert (Seq.equal lhs rhs)
#pop-options


(* ================================================================
   Core pointwise equivalence: [load_block] ≡ [xor_block_into_state].

   For any state, blocks, start, rate:
     load_block rate state blocks start
     == xor_block_into_state state (blocks[start..start+rate]) rate

   Impl side: [load_block]'s hax-proved ensures give the output state
   pointwise.
   Spec side: [xor_block_into_state] is [createi], so [createi_lemma]
   gives pointwise access.
   Byte ranges: [blocks[start..start+rate][8i..8i+8] == blocks[start+8i..start+8i+8]]
   via [lemma_subslice_bytes_eq].
   ================================================================ *)
#push-options "--z3rlimit 200"
let lemma_load_block_eq_xor_block_into_state
      (rate: usize)
      (state: t_Array u64 (mk_usize 25))
      (blocks: t_Slice u8)
      (start: usize)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v start + v rate <= Seq.length #u8 blocks)
      (ensures (
        let block : t_Slice u8 =
          blocks.[ { Core_models.Ops.Range.f_start = start;
                     Core_models.Ops.Range.f_end   = start +! rate } <:
                   Core_models.Ops.Range.t_Range usize ] in
        Libcrux_sha3.Simd.Portable.load_block rate state blocks start
        == Hacspec_sha3.Sponge.xor_block_into_state state block rate))
  = let block : t_Slice u8 =
      blocks.[ { Core_models.Ops.Range.f_start = start;
                 Core_models.Ops.Range.f_end   = start +! rate } <:
               Core_models.Ops.Range.t_Range usize ] in
    let lb = Libcrux_sha3.Simd.Portable.load_block rate state blocks start in
    let spec_state = Hacspec_sha3.Sponge.xor_block_into_state state block rate in
    let byte_eq (i: nat{i < 25}) : Lemma (Seq.index lb i == Seq.index spec_state i) =
      let ii = mk_usize i in
      if v ii < v (rate /! mk_usize 8 <: usize)
      then lemma_subslice_bytes_eq blocks start rate ii
    in
    Classical.forall_intro byte_eq;
    Rust_primitives.Arrays.eq_intro lb spec_state
#pop-options


(* ================================================================
   Step 1: impl_2__absorb_block ≡ spec absorb_block.
   ================================================================ *)
#push-options "--z3rlimit 200"
let lemma_absorb_block_portable
      (rate: usize)
      (ks: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
      (inputs: t_Array (t_Slice u8) (mk_usize 1))
      (start: usize)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v start + v rate <= Seq.length #u8 (inputs.[ mk_usize 0 ]) /\
        Libcrux_sha3.Proof_utils.slices_same_len (mk_usize 1) inputs)
      (ensures
        (Libcrux_sha3.Generic_keccak.impl_2__absorb_block
           (mk_usize 1) #u64 rate ks inputs start)
          .Libcrux_sha3.Generic_keccak.f_st
        ==
        Hacspec_sha3.Sponge.absorb_block
          ks.Libcrux_sha3.Generic_keccak.f_st
          (inputs.[ mk_usize 0 ].[ {
              Core_models.Ops.Range.f_start = start;
              Core_models.Ops.Range.f_end   = start +! rate } <:
            Core_models.Ops.Range.t_Range usize ])
          rate)
  = let state = ks.Libcrux_sha3.Generic_keccak.f_st in
    let input0 = inputs.[ mk_usize 0 ] in
    lemma_load_block_eq_xor_block_into_state rate state input0 start;
    let s1 =
      Libcrux_sha3.Traits.f_load_block
        #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
        #(mk_usize 1)
        #FStar.Tactics.Typeclasses.solve
        rate ks inputs start in
    KP.lemma_keccakf1600_portable s1
#pop-options


(* ================================================================
   Step 2: impl_2__absorb_final ≡ spec absorb_final.

   impl_2__absorb_final 1 #u64 rate delim ks inputs start len
     = f_load_last ... ks inputs start len
     |> impl_2__keccakf1600 1 #u64

   [load_last] internally builds a [rate]-sized padded buffer and calls
   [load_block rate state buffer 0]; the spec's [pad_last_block] builds
   a 200-sized buffer with identical bytes at positions [0..rate].
   Since [xor_block_into_state] only reads positions [< rate], the two
   padded buffers agree on the bytes actually consumed.

   Spec:
     absorb_final state input off len rate delim
     = keccak_f (xor_block_into_state state (pad_last_block ...) rate)

   Proof: same pointwise strategy as [lemma_absorb_block_portable], but
   we step through the internal [load_block] call on the padded buffer.
   ================================================================ *)
(* ----------------------------------------------------------------
   Helper lemma: [load_last] produces the same state as [load_block]
   on the [pad_last_block] output.

   Both constructions build their padded buffer via the same sequence
   of updates:
     * zero-init
     * [update_at_range] with [copy_from_slice input[start..start+len]]
     * [update_at_usize len delim]
     * [update_at_usize (rate-1) (byte | 0x80)]
   They differ only in underlying size (rate vs 200) and agree on
   bytes [0..rate). Since [load_block] reads only bytes [0..rate) of
   its blocks argument (via the pointwise ensures), the two states
   agree.

   Key facts used:
     * [Mem.replace dest src = (src, dest)], so
       [copy_from_slice s src == src] — both copy results are the
       same [blocks[start..start+len]] slice.
     * [update_at_range]'s ensures are slice-level:
         [Seq.slice res 0 f_start == Seq.slice s 0 f_start]
         [Seq.slice res f_start f_end == x]
         [Seq.slice res f_end len == Seq.slice s f_end len]
     * [update_at_usize = Seq.upd].
   ---------------------------------------------------------------- *)
#push-options "--z3rlimit 500 --fuel 1 --ifuel 1"
let lemma_load_last_equals_load_block_on_padded
      (rate: usize)
      (delim: u8)
      (state: t_Array u64 (mk_usize 25))
      (blocks: t_Slice u8)
      (start: usize)
      (len: usize)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v len < v rate /\
        v start + v len <= Seq.length #u8 blocks)
      (ensures
        Libcrux_sha3.Simd.Portable.load_last rate delim state blocks start len
        ==
        Libcrux_sha3.Simd.Portable.load_block rate state
          ((Hacspec_sha3.Sponge.pad_last_block blocks start len rate delim)
             <: t_Slice u8)
          (mk_usize 0))
  = let copy_src : t_Slice u8 =
      blocks.[ { Core_models.Ops.Range.f_start = start;
                 Core_models.Ops.Range.f_end   = start +! len } <:
               Core_models.Ops.Range.t_Range usize ] in
    (* Impl side: mirror load_last's buffer construction. *)
    let b0 : t_Array u8 rate = Rust_primitives.Hax.repeat (mk_u8 0) rate in
    let b1 : t_Array u8 rate =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_range b0
        ({ Core_models.Ops.Range.f_start = mk_usize 0;
           Core_models.Ops.Range.f_end   = len } <:
         Core_models.Ops.Range.t_Range usize)
        (Core_models.Slice.impl__copy_from_slice #u8
            (b0.[ { Core_models.Ops.Range.f_start = mk_usize 0;
                    Core_models.Ops.Range.f_end   = len } <:
                  Core_models.Ops.Range.t_Range usize ] <: t_Slice u8)
            copy_src <: t_Slice u8) in
    let b2 : t_Array u8 rate =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize b1 len delim in
    let b3 : t_Array u8 rate =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize b2
        (rate -! mk_usize 1 <: usize)
        ((b2.[ rate -! mk_usize 1 <: usize ] <: u8) |. mk_u8 128 <: u8) in
    (* Spec side: mirror pad_last_block's buffer construction. *)
    let s0 : t_Array u8 (mk_usize 200) =
      Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 200) in
    let s1 : t_Array u8 (mk_usize 200) =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_range_to s0
        ({ Core_models.Ops.Range.f_end = len } <:
         Core_models.Ops.Range.t_RangeTo usize)
        (Core_models.Slice.impl__copy_from_slice #u8
            (s0.[ { Core_models.Ops.Range.f_end = len } <:
                  Core_models.Ops.Range.t_RangeTo usize ] <: t_Slice u8)
            copy_src <: t_Slice u8) in
    let s2 : t_Array u8 (mk_usize 200) =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s1 len delim in
    let s3 : t_Array u8 (mk_usize 200) =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s2
        (rate -! mk_usize 1 <: usize)
        ((s2.[ rate -! mk_usize 1 <: usize ] <: u8) |. mk_u8 128 <: u8) in
    (* Slice-level facts from update_at_range / update_at_range_to ensures. *)
    assert (Seq.slice (b1 <: Seq.seq u8) 0 (v len) == copy_src);
    assert (Seq.slice (b1 <: Seq.seq u8) (v len) (v rate)
            == Seq.slice (b0 <: Seq.seq u8) (v len) (v rate));
    assert (Seq.slice (s1 <: Seq.seq u8) 0 (v len) == copy_src);
    assert (Seq.slice (s1 <: Seq.seq u8) (v len) 200
            == Seq.slice (s0 <: Seq.seq u8) (v len) 200);
    (* Zeros on the tail of b0/s0. *)
    assert (forall (k: nat). k < v rate ==> Seq.index (b0 <: Seq.seq u8) k == mk_u8 0);
    assert (forall (k: nat). k < 200 ==> Seq.index (s0 <: Seq.seq u8) k == mk_u8 0);
    (* Byte-level equality on [0..rate) between b1 and s1 via slice ensures. *)
    let b1_s1_byte_eq (m: nat{m < v rate})
      : Lemma (Seq.index (b1 <: Seq.seq u8) m == Seq.index (s1 <: Seq.seq u8) m)
      = if m < v len then begin
          Seq.lemma_index_slice (b1 <: Seq.seq u8) 0 (v len) m;
          Seq.lemma_index_slice (s1 <: Seq.seq u8) 0 (v len) m
        end
        else begin
          Seq.lemma_index_slice (b1 <: Seq.seq u8) (v len) (v rate) (m - v len);
          Seq.lemma_index_slice (s1 <: Seq.seq u8) (v len) 200 (m - v len);
          Seq.lemma_index_slice (b0 <: Seq.seq u8) (v len) (v rate) (m - v len);
          Seq.lemma_index_slice (s0 <: Seq.seq u8) (v len) 200 (m - v len)
        end
    in
    Classical.forall_intro b1_s1_byte_eq;
    (* Lift to b2/s2 and b3/s3 via Seq.upd (update_at_usize = Seq.upd). *)
    let b3_s3_byte_eq (m: nat{m < v rate})
      : Lemma (Seq.index (b3 <: Seq.seq u8) m == Seq.index (s3 <: Seq.seq u8) m)
      = () in
    Classical.forall_intro b3_s3_byte_eq;
    (* load_block's ensures on both sides: pointwise output equality. *)
    let impl_out = Libcrux_sha3.Simd.Portable.load_block rate state
                     (b3 <: t_Slice u8) (mk_usize 0) in
    let spec_out = Libcrux_sha3.Simd.Portable.load_block rate state
                     (s3 <: t_Slice u8) (mk_usize 0) in
    let lane_eq (i: nat{i < 25})
      : Lemma (Seq.index impl_out i == Seq.index spec_out i)
      = if v (mk_usize i) < v (rate /! mk_usize 8 <: usize) then begin
          let impl_slice : t_Slice u8 =
            (b3 <: t_Slice u8).[ {
              Core_models.Ops.Range.f_start =
                (mk_usize 0) +! (mk_usize 8 *! (mk_usize i) <: usize);
              Core_models.Ops.Range.f_end   =
                ((mk_usize 0) +! (mk_usize 8 *! (mk_usize i) <: usize) <: usize)
                +! mk_usize 8
            } <: Core_models.Ops.Range.t_Range usize ] in
          let spec_slice : t_Slice u8 =
            (s3 <: t_Slice u8).[ {
              Core_models.Ops.Range.f_start =
                (mk_usize 0) +! (mk_usize 8 *! (mk_usize i) <: usize);
              Core_models.Ops.Range.f_end   =
                ((mk_usize 0) +! (mk_usize 8 *! (mk_usize i) <: usize) <: usize)
                +! mk_usize 8
            } <: Core_models.Ops.Range.t_Range usize ] in
          assert (Seq.equal impl_slice spec_slice)
        end
    in
    Classical.forall_intro lane_eq;
    Rust_primitives.Arrays.eq_intro impl_out spec_out
#pop-options


(* Compose helper + load_block≡xor bridge into one high-level equation:
   [load_last] on the raw message is equivalent to [xor_block_into_state]
   applied to [pad_last_block]. Closing the gap between the two spec
   forms ([0..rate) slice vs full 200-byte array) uses the fact that
   [xor_block_into_state] reads only bytes [0..rate). *)
#push-options "--z3rlimit 400"
let lemma_load_last_eq_xor_block_into_state_padded
      (rate: usize)
      (delim: u8)
      (state: t_Array u64 (mk_usize 25))
      (blocks: t_Slice u8)
      (start: usize)
      (len: usize)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v len < v rate /\
        v start + v len <= Seq.length #u8 blocks)
      (ensures
        Libcrux_sha3.Simd.Portable.load_last rate delim state blocks start len
        ==
        Hacspec_sha3.Sponge.xor_block_into_state state
          ((Hacspec_sha3.Sponge.pad_last_block blocks start len rate delim)
             <: t_Slice u8)
          rate)
  = let spec_buffer : t_Array u8 (mk_usize 200) =
      Hacspec_sha3.Sponge.pad_last_block blocks start len rate delim in
    let full : t_Slice u8 = spec_buffer in
    lemma_load_last_equals_load_block_on_padded rate delim state blocks start len;
    lemma_load_block_eq_xor_block_into_state rate state full (mk_usize 0);
    (* Now: load_last == xor_block_into_state state (full[0..rate]) rate;
       spec gives xor_block_into_state state full rate.
       Both createi forms read full[8i..8i+8] — equal up to rate. *)
    let prefix : t_Slice u8 =
      full.[ { Core_models.Ops.Range.f_start = mk_usize 0;
               Core_models.Ops.Range.f_end   = (mk_usize 0) +! rate } <:
             Core_models.Ops.Range.t_Range usize ] in
    let r_prefix = Hacspec_sha3.Sponge.xor_block_into_state state prefix rate in
    let r_full   = Hacspec_sha3.Sponge.xor_block_into_state state full rate in
    let lane_eq (i: nat{i < 25}) : Lemma (Seq.index r_prefix i == Seq.index r_full i) =
      let ii = mk_usize i in
      if v ii < v (rate /! mk_usize 8 <: usize)
      then begin
        let lhs : t_Slice u8 =
          prefix.[ { Core_models.Ops.Range.f_start = mk_usize 8 *! ii;
                     Core_models.Ops.Range.f_end   =
                       (mk_usize 8 *! ii <: usize) +! mk_usize 8 } <:
                   Core_models.Ops.Range.t_Range usize ] in
        let rhs : t_Slice u8 =
          full.[ { Core_models.Ops.Range.f_start = mk_usize 8 *! ii;
                   Core_models.Ops.Range.f_end   =
                     (mk_usize 8 *! ii <: usize) +! mk_usize 8 } <:
                 Core_models.Ops.Range.t_Range usize ] in
        assert (Seq.equal lhs rhs)
      end
    in
    Classical.forall_intro lane_eq;
    Rust_primitives.Arrays.eq_intro r_prefix r_full
#pop-options


(* ================================================================
   Step 2: impl_2__absorb_final ≡ spec absorb_final.
   ================================================================ *)
#push-options "--z3rlimit 200"
let lemma_absorb_last_portable
      (rate: usize)
      (delim: u8)
      (ks: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
      (inputs: t_Array (t_Slice u8) (mk_usize 1))
      (start: usize)
      (len: usize)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v len < v rate /\
        v start + v len <= Seq.length #u8 (inputs.[ mk_usize 0 ]) /\
        Libcrux_sha3.Proof_utils.slices_same_len (mk_usize 1) inputs)
      (ensures
        (Libcrux_sha3.Generic_keccak.impl_2__absorb_final
           (mk_usize 1) #u64 rate delim ks inputs start len)
          .Libcrux_sha3.Generic_keccak.f_st
        ==
        Hacspec_sha3.Sponge.absorb_final
          ks.Libcrux_sha3.Generic_keccak.f_st
          (inputs.[ mk_usize 0 ])
          start len rate delim)
  = let state = ks.Libcrux_sha3.Generic_keccak.f_st in
    let input0 = inputs.[ mk_usize 0 ] in
    lemma_load_last_eq_xor_block_into_state_padded rate delim state input0 start len;
    let s1 =
      Libcrux_sha3.Traits.f_load_last
        #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
        #(mk_usize 1)
        #FStar.Tactics.Typeclasses.solve
        rate delim ks inputs start len in
    KP.lemma_keccakf1600_portable s1
#pop-options


(* ================================================================
   Step 3: a full-rate squeeze block preceded by a permutation.

   Matches one iteration of the [1 .. output_blocks) middle-loop in
   both [Libcrux_sha3.Generic_keccak.Portable.squeeze] and
   [Hacspec_sha3.Sponge.squeeze]:

     impl side: keccakf1600 ; f_squeeze (start, RATE)
     spec side: keccak_f   ; squeeze_state (start, RATE)

   Both sides produce the same new state (after keccak_f) and the
   same output slice.
   ================================================================ *)
let lemma_squeeze_block_portable
      (rate: usize)
      (ks: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
      (out: t_Slice u8)
      (start: usize)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v start + v rate <= Seq.length #u8 out)
      (ensures (
        let ks' = Libcrux_sha3.Generic_keccak.impl_2__keccakf1600
                    (mk_usize 1) #u64 ks in
        let out' = Libcrux_sha3.Traits.f_squeeze
                     #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
                     #u64
                     #FStar.Tactics.Typeclasses.solve
                     rate ks' out start rate in
        let state' = Hacspec_sha3.Keccak_f.keccak_f
                       ks.Libcrux_sha3.Generic_keccak.f_st in
        ks'.Libcrux_sha3.Generic_keccak.f_st == state' /\
        out' == Hacspec_sha3.Sponge.squeeze_state state' out start rate))
  = let state  = ks.Libcrux_sha3.Generic_keccak.f_st in
    KP.lemma_keccakf1600_portable ks;
    let ks' = Libcrux_sha3.Generic_keccak.impl_2__keccakf1600
                (mk_usize 1) #u64 ks in
    let state' = ks'.Libcrux_sha3.Generic_keccak.f_st in
    (* store_block at l=0 via the Sponge.Portable admit (collapses to identity). *)
    let outputs : t_Array (t_Slice u8) (mk_usize 1) =
      let list = [out] in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
      Rust_primitives.Hax.array_of_list 1 list in
    assert (outputs.[ mk_usize 0 ] == out);
    SP.portable_sc_store_block rate state' outputs start rate 0;
    KP.lemma_extract_lane_portable_identity state'


(* ================================================================
   Step 4: a partial-rate trailing squeeze preceded by a permutation.

   Matches the [output_rem ≠ 0] tail branch in both
   [Libcrux_sha3.Generic_keccak.Portable.squeeze] and
   [Hacspec_sha3.Sponge.squeeze]:

     impl side: keccakf1600 ; f_squeeze (start, len)    with len < rate
     spec side: keccak_f   ; squeeze_state (start, len) with len < rate
   ================================================================ *)
let lemma_squeeze_last_portable
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
        let ks' = Libcrux_sha3.Generic_keccak.impl_2__keccakf1600
                    (mk_usize 1) #u64 ks in
        let out' = Libcrux_sha3.Traits.f_squeeze
                     #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
                     #u64
                     #FStar.Tactics.Typeclasses.solve
                     rate ks' out start len in
        let state' = Hacspec_sha3.Keccak_f.keccak_f
                       ks.Libcrux_sha3.Generic_keccak.f_st in
        ks'.Libcrux_sha3.Generic_keccak.f_st == state' /\
        out' == Hacspec_sha3.Sponge.squeeze_state state' out start len))
  = KP.lemma_keccakf1600_portable ks;
    let ks' = Libcrux_sha3.Generic_keccak.impl_2__keccakf1600
                (mk_usize 1) #u64 ks in
    let state' = ks'.Libcrux_sha3.Generic_keccak.f_st in
    let outputs : t_Array (t_Slice u8) (mk_usize 1) =
      let list = [out] in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
      Rust_primitives.Hax.array_of_list 1 list in
    assert (outputs.[ mk_usize 0 ] == out);
    SP.portable_sc_store_block rate state' outputs start len 0;
    KP.lemma_extract_lane_portable_identity state'
