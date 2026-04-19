module EquivImplSpec.Sponge.Arm64

(* ================================================================
   NEON (Arm64, N=2, v_T=t_e_uint64x2_t) instantiation of the generic
   sponge-layer equivalence proof.

   Builds a [sponge_correctness] record for
   [Libcrux_sha3.Simd.Arm64.{impl_1, impl_2}]:
     - t_Absorb  at N=2 on t_KeccakState 2 t_e_uint64x2_t
     - t_Squeeze2 at N=2 (two output slices)

   The three per-backend lemmas — sc_load_block, sc_load_last,
   sc_store_block — are admitted. Their proofs will unfold the NEON
   t_Absorb / t_Squeeze2 methods, push [arm64_lane] through the
   per-intrinsic postconditions declared in [Libcrux_intrinsics.
   Arm64_extract], and reduce to the scalar xor_block_into_state /
   squeeze_state on the extracted lane.
   ================================================================ *)

#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"

open FStar.Mul
open Core_models

module G  = EquivImplSpec.Keccakf.Generic
module KA = EquivImplSpec.Keccakf.Arm64
module SC = EquivImplSpec.Sponge.Generic.Core
module I  = Libcrux_intrinsics.Arm64_extract

(* Bring Arm64 typeclass instances into scope. *)
let _ =
  let open Libcrux_intrinsics.Arm64_extract in
  let open Libcrux_sha3.Traits in
  let open Libcrux_sha3.Simd.Arm64 in
  ()

(* ================================================================
   sq_lane for N=2: the Arm64 squeeze is t_Squeeze2.f_squeeze2 which
   returns a pair of output slices. Lane 0 is the first component,
   lane 1 the second.
   ================================================================ *)

let sq_lane_arm64
      (rate: usize)
      (state: t_Array I.t_e_uint64x2_t (mk_usize 25))
      (outputs: t_Array (t_Slice u8) (mk_usize 2))
      (start: usize)
      (len: usize)
      (l: nat{l < 2})
  : Pure (t_Slice u8)
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v len <= v rate /\
        v start + v len <= Seq.length #u8 (outputs.[ mk_usize 0 ]) /\
        Libcrux_sha3.Proof_utils.slices_same_len (mk_usize 2) outputs)
      (ensures fun r -> Seq.length #u8 r == Seq.length #u8 (outputs.[ mk_usize l ]))
  = let pair =
      Libcrux_sha3.Traits.f_squeeze2
        #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2) I.t_e_uint64x2_t)
        #I.t_e_uint64x2_t
        #FStar.Tactics.Typeclasses.solve
        rate
        ({ Libcrux_sha3.Generic_keccak.f_st = state }
           <: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2) I.t_e_uint64x2_t)
        (outputs.[ mk_usize 0 ])
        (outputs.[ mk_usize 1 ])
        start
        len
    in
    let out0, out1 = pair in
    if l = 0 then out0 else out1

(* ================================================================
   Admitted per-backend lemmas — reduce f_load_block / f_load_last /
   f_squeeze2 on the Arm64 impl to the scalar spec operations on the
   extracted lane.
   ================================================================ *)

let arm64_sc_load_block
      (rate: usize)
      (state: t_Array I.t_e_uint64x2_t (mk_usize 25))
      (inputs: t_Array (t_Slice u8) (mk_usize 2))
      (start: usize)
      (l: nat{l < 2})
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v start + v rate <= Seq.length #u8 (inputs.[ mk_usize 0 ]) /\
        Libcrux_sha3.Proof_utils.slices_same_len (mk_usize 2) inputs)
      (ensures
        G.extract_lane (mk_usize 2) KA.lc_arm64
          (Libcrux_sha3.Traits.f_load_block
             #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2) I.t_e_uint64x2_t)
             #(mk_usize 2)
             #FStar.Tactics.Typeclasses.solve
             rate
             ({ Libcrux_sha3.Generic_keccak.f_st = state }
                <: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2) I.t_e_uint64x2_t)
             inputs
             start)
            .Libcrux_sha3.Generic_keccak.f_st
          l
        ==
        Hacspec_sha3.Sponge.xor_block_into_state
          (G.extract_lane (mk_usize 2) KA.lc_arm64 state l)
          (inputs.[ mk_usize l ].[ {
              Core_models.Ops.Range.f_start = start;
              Core_models.Ops.Range.f_end   = start +! rate } <:
            Core_models.Ops.Range.t_Range usize ])
          rate)
  = admit ()

let arm64_sc_load_last
      (rate: usize)
      (delim: u8)
      (state: t_Array I.t_e_uint64x2_t (mk_usize 25))
      (inputs: t_Array (t_Slice u8) (mk_usize 2))
      (start: usize)
      (len: usize)
      (l: nat{l < 2})
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v len < v rate /\
        v start + v len <= Seq.length #u8 (inputs.[ mk_usize 0 ]) /\
        Libcrux_sha3.Proof_utils.slices_same_len (mk_usize 2) inputs)
      (ensures (
        let padded: t_Array u8 (mk_usize 200) =
          Hacspec_sha3.Sponge.pad_last_block
            (inputs.[ mk_usize l ]) start len rate delim
        in
        G.extract_lane (mk_usize 2) KA.lc_arm64
          (Libcrux_sha3.Traits.f_load_last
             #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2) I.t_e_uint64x2_t)
             #(mk_usize 2)
             #FStar.Tactics.Typeclasses.solve
             rate delim
             ({ Libcrux_sha3.Generic_keccak.f_st = state }
                <: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2) I.t_e_uint64x2_t)
             inputs
             start
             len)
            .Libcrux_sha3.Generic_keccak.f_st
          l
        ==
        Hacspec_sha3.Sponge.xor_block_into_state
          (G.extract_lane (mk_usize 2) KA.lc_arm64 state l)
          (padded.[ { Core_models.Ops.Range.f_start = mk_usize 0;
                      Core_models.Ops.Range.f_end   = rate } <:
                    Core_models.Ops.Range.t_Range usize ] <: t_Slice u8)
          rate))
  = admit ()

let arm64_sc_store_block
      (rate: usize)
      (state: t_Array I.t_e_uint64x2_t (mk_usize 25))
      (outputs: t_Array (t_Slice u8) (mk_usize 2))
      (start: usize)
      (len: usize)
      (l: nat{l < 2})
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v len <= v rate /\
        v start + v len <= Seq.length #u8 (outputs.[ mk_usize 0 ]) /\
        Libcrux_sha3.Proof_utils.slices_same_len (mk_usize 2) outputs)
      (ensures
        sq_lane_arm64 rate state outputs start len l
        ==
        Hacspec_sha3.Sponge.squeeze_state
          (G.extract_lane (mk_usize 2) KA.lc_arm64 state l)
          (outputs.[ mk_usize l ] <: t_Slice u8)
          start
          len)
  = admit ()

(* ================================================================
   Assemble the [sponge_correctness] record for Arm64.

   The sponge_correctness record requires a [t_Absorb ... v_N] dictionary
   in scope — the Arm64 impl_1 at N=2 is tcresolved automatically.
   ================================================================ *)

let sc_arm64 : SC.sponge_correctness (mk_usize 2) #I.t_e_uint64x2_t KA.lc_arm64 =
  {
    sq_lane        = sq_lane_arm64;
    sc_load_block  = arm64_sc_load_block;
    sc_load_last   = arm64_sc_load_last;
    sc_store_block = arm64_sc_store_block;
  }
