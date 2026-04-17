module EquivImplSpec.Sponge.Core
(* ================================================================
   Sponge-layer equivalence between the libcrux SHA-3 implementation
   and the hacspec specification.

   Builds on EquivImplSpec.Keccakf.lemma_keccakf1600_equiv:
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
   Phase 10: Lane Index Equivalence (post FIPS-native layout flip)

   After the FIPS-native layout flip, [lane_index] was removed from
   the spec (it collapsed to the identity). The impl writes lane [i]
   at flat index [5*(i/5) + i%5 = i] under
   [get_ij(N, state, i/5, i%5) = state[5*(i/5) + i%5]].
   ================================================================ *)

let lemma_lane_index_is_impl_index (i: usize)
  : Lemma (requires v i < 25)
          (ensures  i ==
                    (mk_usize 5 *! (i /! mk_usize 5 <: usize) <: usize) +!
                    (i %! mk_usize 5 <: usize))
  = ()

