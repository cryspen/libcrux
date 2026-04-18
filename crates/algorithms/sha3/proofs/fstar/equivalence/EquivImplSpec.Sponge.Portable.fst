module EquivImplSpec.Sponge.Portable

(* ================================================================
   Portable (N=1, v_T=u64) instantiation of the generic sponge-layer
   equivalence proof.

   Builds a [sponge_correctness] record for
   [Libcrux_sha3.Simd.Portable.{impl_1, impl_2}]: the t_Absorb and
   t_Squeeze typeclass instances at N=1.

   The three per-backend lemmas — sc_load_block, sc_load_last,
   sc_store_block — are admitted here. They reduce to:
     f_load_block / f_load_last  ≡ scalar xor_block_into_state
     f_squeeze                   ≡ scalar squeeze_state
   under the N=1 identity for extract_lane. Discharging them is the
   content of the portable sponge-layer proof already carried out in
   [EquivImplSpec.Sponge.Absorb] / [.Squeeze]; they should be closable
   by composing those lemmas with [lemma_extract_lane_portable_identity].
   ================================================================ *)

#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"

open FStar.Mul
open Core_models

module G  = EquivImplSpec.Keccakf.Generic
module P  = EquivImplSpec.Keccakf.Portable
module SC = EquivImplSpec.Sponge.Generic.Core
module A  = EquivImplSpec.Sponge.Generic.Absorb
module S  = EquivImplSpec.Sponge.Generic.Squeeze

(* Bring Portable typeclass instances into scope. *)
let _ =
  let open Libcrux_sha3.Traits in
  let open Libcrux_sha3.Simd.Portable in
  ()

(* ================================================================
   sq_lane for N=1: single-lane squeeze via t_Squeeze.f_squeeze.
   ================================================================ *)

let sq_lane_portable
      (rate: usize)
      (state: t_Array u64 (mk_usize 25))
      (outputs: t_Array (t_Slice u8) (mk_usize 1))
      (start: usize)
      (len: usize)
      (l: nat{l < 1})
  : Pure (t_Slice u8)
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v len <= v rate /\
        v start + v len <= Seq.length #u8 (outputs.[ mk_usize 0 ]) /\
        Libcrux_sha3.Proof_utils.slices_same_len (mk_usize 1) outputs)
      (ensures fun r -> Seq.length #u8 r == Seq.length #u8 (outputs.[ mk_usize l ]))
  = Libcrux_sha3.Traits.f_squeeze
      #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
      #u64
      #FStar.Tactics.Typeclasses.solve
      rate
      ({ Libcrux_sha3.Generic_keccak.f_st = state }
         <: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
      (outputs.[ mk_usize 0 ])
      start
      len

(* ================================================================
   Bridge lemmas: pointwise equivalence of the Portable [load_block]
   and [load_last] with the scalar spec [xor_block_into_state] (a
   [createi] on the extraction side).

   These closed lemmas are reused from [Sponge.Portable.Steps.fst] and
   from the [sc_load_block] / [sc_load_last] admits below.
   ================================================================ *)

(* Slice-of-slice byte equality:
   (blocks[start..start+rate])[8k..8k+8] == blocks[start+8k..start+8k+8] *)
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

(* Core pointwise equivalence: [load_block] ≡ [xor_block_into_state]. *)
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

(* Helper: [load_last] = [load_block] on [pad_last_block]. *)
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
    assert (Seq.slice (b1 <: Seq.seq u8) 0 (v len) == copy_src);
    assert (Seq.slice (b1 <: Seq.seq u8) (v len) (v rate)
            == Seq.slice (b0 <: Seq.seq u8) (v len) (v rate));
    assert (Seq.slice (s1 <: Seq.seq u8) 0 (v len) == copy_src);
    assert (Seq.slice (s1 <: Seq.seq u8) (v len) 200
            == Seq.slice (s0 <: Seq.seq u8) (v len) 200);
    assert (forall (k: nat). k < v rate ==> Seq.index (b0 <: Seq.seq u8) k == mk_u8 0);
    assert (forall (k: nat). k < 200 ==> Seq.index (s0 <: Seq.seq u8) k == mk_u8 0);
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
    let b3_s3_byte_eq (m: nat{m < v rate})
      : Lemma (Seq.index (b3 <: Seq.seq u8) m == Seq.index (s3 <: Seq.seq u8) m)
      = () in
    Classical.forall_intro b3_s3_byte_eq;
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

(* Compose: [load_last] ≡ [xor_block_into_state] on [pad_last_block]. *)
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
   Per-backend lemmas — reduce f_load_block / f_load_last / f_squeeze
   on the Portable impl to the scalar spec operations.
   ================================================================ *)

let portable_sc_load_block
      (rate: usize)
      (state: t_Array u64 (mk_usize 25))
      (inputs: t_Array (t_Slice u8) (mk_usize 1))
      (start: usize)
      (l: nat{l < 1})
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v start + v rate <= Seq.length #u8 (inputs.[ mk_usize 0 ]) /\
        Libcrux_sha3.Proof_utils.slices_same_len (mk_usize 1) inputs)
      (ensures
        G.extract_lane (mk_usize 1) P.lc_portable
          (Libcrux_sha3.Traits.f_load_block
             #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
             #(mk_usize 1)
             #FStar.Tactics.Typeclasses.solve
             rate
             ({ Libcrux_sha3.Generic_keccak.f_st = state }
                <: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
             inputs
             start)
            .Libcrux_sha3.Generic_keccak.f_st
          l
        ==
        Hacspec_sha3.Sponge.xor_block_into_state
          (G.extract_lane (mk_usize 1) P.lc_portable state l)
          (inputs.[ mk_usize l ].[ {
              Core_models.Ops.Range.f_start = start;
              Core_models.Ops.Range.f_end   = start +! rate } <:
            Core_models.Ops.Range.t_Range usize ])
          rate)
  = let input0 = inputs.[ mk_usize 0 ] in
    lemma_load_block_eq_xor_block_into_state rate state input0 start;
    P.lemma_extract_lane_portable_identity state;
    let ks : Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 =
      { Libcrux_sha3.Generic_keccak.f_st = state } in
    let result =
      Libcrux_sha3.Traits.f_load_block
        #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
        #(mk_usize 1)
        #FStar.Tactics.Typeclasses.solve
        rate ks inputs start in
    P.lemma_extract_lane_portable_identity
      result.Libcrux_sha3.Generic_keccak.f_st

let portable_sc_load_last
      (rate: usize)
      (delim: u8)
      (state: t_Array u64 (mk_usize 25))
      (inputs: t_Array (t_Slice u8) (mk_usize 1))
      (start: usize)
      (len: usize)
      (l: nat{l < 1})
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v len < v rate /\
        v start + v len <= Seq.length #u8 (inputs.[ mk_usize 0 ]) /\
        Libcrux_sha3.Proof_utils.slices_same_len (mk_usize 1) inputs)
      (ensures (
        let padded: t_Array u8 (mk_usize 200) =
          Hacspec_sha3.Sponge.pad_last_block
            (inputs.[ mk_usize l ]) start len rate delim
        in
        G.extract_lane (mk_usize 1) P.lc_portable
          (Libcrux_sha3.Traits.f_load_last
             #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
             #(mk_usize 1)
             #FStar.Tactics.Typeclasses.solve
             rate delim
             ({ Libcrux_sha3.Generic_keccak.f_st = state }
                <: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
             inputs
             start
             len)
            .Libcrux_sha3.Generic_keccak.f_st
          l
        ==
        Hacspec_sha3.Sponge.xor_block_into_state
          (G.extract_lane (mk_usize 1) P.lc_portable state l)
          (padded <: t_Slice u8)
          rate))
  = let input0 = inputs.[ mk_usize 0 ] in
    lemma_load_last_eq_xor_block_into_state_padded
      rate delim state input0 start len;
    P.lemma_extract_lane_portable_identity state;
    let ks : Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 =
      { Libcrux_sha3.Generic_keccak.f_st = state } in
    let result =
      Libcrux_sha3.Traits.f_load_last
        #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
        #(mk_usize 1)
        #FStar.Tactics.Typeclasses.solve
        rate delim ks inputs start len in
    P.lemma_extract_lane_portable_identity
      result.Libcrux_sha3.Generic_keccak.f_st

let portable_sc_store_block
      (rate: usize)
      (state: t_Array u64 (mk_usize 25))
      (outputs: t_Array (t_Slice u8) (mk_usize 1))
      (start: usize)
      (len: usize)
      (l: nat{l < 1})
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v len <= v rate /\
        v start + v len <= Seq.length #u8 (outputs.[ mk_usize 0 ]) /\
        Libcrux_sha3.Proof_utils.slices_same_len (mk_usize 1) outputs)
      (ensures
        sq_lane_portable rate state outputs start len l
        ==
        Hacspec_sha3.Sponge.squeeze_state
          (G.extract_lane (mk_usize 1) P.lc_portable state l)
          (outputs.[ mk_usize l ] <: t_Slice u8)
          start
          len)
  = admit ()

(* ================================================================
   Assemble the [sponge_correctness] record for Portable.
   ================================================================ *)

let sc_portable : SC.sponge_correctness (mk_usize 1) #u64 P.lc_portable =
  {
    sq_lane        = sq_lane_portable;
    sc_load_block  = portable_sc_load_block;
    sc_load_last   = portable_sc_load_last;
    sc_store_block = portable_sc_store_block;
  }
