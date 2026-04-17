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
   Admitted per-backend lemmas — reduce f_load_block / f_load_last /
   f_squeeze on the Portable impl to the scalar spec operations.
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
  = admit ()

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
  = admit ()

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
