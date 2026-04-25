module EquivImplSpec.Sponge.Avx2

(* ================================================================
   AVX2 (N=4, v_T=t_Vec256) instantiation of the generic sponge-layer
   equivalence proof.

   Mirrors [EquivImplSpec.Sponge.Arm64] at N=4.

   STRUCTURAL DIFFERENCE FROM Arm64:
   The three per-backend lemmas — sc_load_block, sc_load_last,
   sc_store_block — are ADMITTED for AVX2, in contrast to the Arm64
   versions which are proved by reducing to per-u64-lane ensures on
   the underlying NEON intrinsics.  The AVX2 stubs in
   [Libcrux_intrinsics.Avx2_extract] expose only bit_vec-level
   semantics with no per-u64-lane ensures, so the analogous reduction
   is not currently possible.

   Discharging these three primitives requires either:
     (a) adding per-u64-lane ensures to mm256_xor_si256,
         mm256_storeu_si256_u8, mm256_loadu_si256_u8, etc., in
         [BitVec.Intrinsics] / [Libcrux_intrinsics.Avx2_extract], or
     (b) admitting them at the AVX2 source level
         (which is what [Libcrux_sha3.Simd.Avx2.{load_block, load_last,
         store_block}] effectively does already via body-level
         [hax_lib::fstar!("admit()")]).

   Once the three are admitted, the [sponge_correctness] record
   [sc_avx2] is built from them and used downstream by
   [EquivImplSpec.Sponge.Avx2.Steps].
   ================================================================ *)

#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"

open FStar.Mul
open Core_models

module G  = EquivImplSpec.Keccakf.Generic
module KA = EquivImplSpec.Keccakf.Avx2
module SC = EquivImplSpec.Sponge.Generic.Core
module I  = Libcrux_intrinsics.Avx2_extract

(* Bring AVX2 typeclass instances into scope. *)
let _ =
  let open Libcrux_intrinsics.Avx2_extract in
  let open Libcrux_sha3.Traits in
  let open Libcrux_sha3.Simd.Avx2 in
  ()

(* ================================================================
   sq_lane for N=4: the AVX2 squeeze is t_Squeeze4.f_squeeze4 which
   returns a 4-tuple of output slices. Lane l is the l-th component.
   ================================================================ *)

let sq_lane_avx2
      (rate: usize)
      (state: t_Array I.t_Vec256 (mk_usize 25))
      (outputs: t_Array (t_Slice u8) (mk_usize 4))
      (start: usize)
      (len: usize)
      (l: nat{l < 4})
  : Pure (t_Slice u8)
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v len <= v rate /\
        v start + v len <= Seq.length #u8 (outputs.[ mk_usize 0 ]) /\
        Libcrux_sha3.Proof_utils.slices_same_len (mk_usize 4) outputs)
      (ensures fun r -> Seq.length #u8 r == Seq.length #u8 (outputs.[ mk_usize l ]))
  = let tup =
      Libcrux_sha3.Traits.f_squeeze4
        #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 4) I.t_Vec256)
        #I.t_Vec256
        #FStar.Tactics.Typeclasses.solve
        rate
        ({ Libcrux_sha3.Generic_keccak.f_st = state }
           <: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 4) I.t_Vec256)
        (outputs.[ mk_usize 0 ])
        (outputs.[ mk_usize 1 ])
        (outputs.[ mk_usize 2 ])
        (outputs.[ mk_usize 3 ])
        start
        len
    in
    let out0, out1, out2, out3 = tup in
    if l = 0 then out0
    else if l = 1 then out1
    else if l = 2 then out2
    else out3

(* ================================================================
   ADMITTED per-backend bridges.

   Each is the AVX2 analogue of the proved arm64_sc_* lemmas in
   [EquivImplSpec.Sponge.Arm64].  They are admitted because the AVX2
   intrinsics do not currently expose per-u64-lane ensures.
   ================================================================ *)

let avx2_sc_load_block
      (rate: usize)
      (state: t_Array I.t_Vec256 (mk_usize 25))
      (inputs: t_Array (t_Slice u8) (mk_usize 4))
      (start: usize)
      (l: nat{l < 4})
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v start + v rate <= Seq.length #u8 (inputs.[ mk_usize 0 ]) /\
        Libcrux_sha3.Proof_utils.slices_same_len (mk_usize 4) inputs)
      (ensures
        G.extract_lane (mk_usize 4) KA.lc_avx2
          (Libcrux_sha3.Traits.f_load_block
             #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 4) I.t_Vec256)
             #(mk_usize 4)
             #FStar.Tactics.Typeclasses.solve
             rate
             ({ Libcrux_sha3.Generic_keccak.f_st = state }
                <: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 4) I.t_Vec256)
             inputs
             start)
            .Libcrux_sha3.Generic_keccak.f_st
          l
        ==
        Hacspec_sha3.Sponge.xor_block_into_state
          (G.extract_lane (mk_usize 4) KA.lc_avx2 state l)
          (inputs.[ mk_usize l ].[ {
              Core_models.Ops.Range.f_start = start;
              Core_models.Ops.Range.f_end   = start +! rate } <:
            Core_models.Ops.Range.t_Range usize ])
          rate)
  = admit ()

let avx2_sc_load_last
      (rate: usize)
      (delim: u8)
      (state: t_Array I.t_Vec256 (mk_usize 25))
      (inputs: t_Array (t_Slice u8) (mk_usize 4))
      (start: usize)
      (len: usize)
      (l: nat{l < 4})
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v len < v rate /\
        v start + v len <= Seq.length #u8 (inputs.[ mk_usize 0 ]) /\
        Libcrux_sha3.Proof_utils.slices_same_len (mk_usize 4) inputs)
      (ensures (
        let padded: t_Array u8 (mk_usize 200) =
          Hacspec_sha3.Sponge.pad_last_block
            (inputs.[ mk_usize l ]) start len rate delim
        in
        G.extract_lane (mk_usize 4) KA.lc_avx2
          (Libcrux_sha3.Traits.f_load_last
             #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 4) I.t_Vec256)
             #(mk_usize 4)
             #FStar.Tactics.Typeclasses.solve
             rate delim
             ({ Libcrux_sha3.Generic_keccak.f_st = state }
                <: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 4) I.t_Vec256)
             inputs
             start
             len)
            .Libcrux_sha3.Generic_keccak.f_st
          l
        ==
        Hacspec_sha3.Sponge.xor_block_into_state
          (G.extract_lane (mk_usize 4) KA.lc_avx2 state l)
          (padded.[ { Core_models.Ops.Range.f_start = mk_usize 0;
                      Core_models.Ops.Range.f_end   = rate } <:
                    Core_models.Ops.Range.t_Range usize ] <: t_Slice u8)
          rate))
  = admit ()

let avx2_sc_store_block
      (rate: usize)
      (state: t_Array I.t_Vec256 (mk_usize 25))
      (outputs: t_Array (t_Slice u8) (mk_usize 4))
      (start: usize)
      (len: usize)
      (l: nat{l < 4})
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v len <= v rate /\
        v start + v len <= Seq.length #u8 (outputs.[ mk_usize 0 ]) /\
        Libcrux_sha3.Proof_utils.slices_same_len (mk_usize 4) outputs)
      (ensures
        sq_lane_avx2 rate state outputs start len l
        ==
        Hacspec_sha3.Sponge.squeeze_state
          (Core_models.Slice.impl__len #u8 (outputs.[ mk_usize l ]))
          (G.extract_lane (mk_usize 4) KA.lc_avx2 state l)
          (outputs.[ mk_usize l ] <: t_Array u8 _)
          start
          len)
  = admit ()

(* ================================================================
   Assemble the [sponge_correctness] record for AVX2.
   ================================================================ *)

let sc_avx2 : SC.sponge_correctness (mk_usize 4) #I.t_Vec256 KA.lc_avx2 =
  {
    sq_lane        = sq_lane_avx2;
    sc_load_block  = avx2_sc_load_block;
    sc_load_last   = avx2_sc_load_last;
    sc_store_block = avx2_sc_store_block;
  }
