module EquivImplSpec.Sponge.Arm64.API

(* ================================================================
   Top-level SHA-3 / SHAKE equivalence theorems for the Arm64
   (N=2, v_T=t_e_uint64x2_t) backend.

   STRUCTURAL DIFFERENCE FROM Sponge.Portable.API:

   The Arm64 top-level hashers in [Libcrux_sha3.Neon] dispatch
   through a two-lane driver [Libcrux_sha3.Generic_keccak.Simd128.keccak2],
   e.g.

       let sha256 digest data =
         let dummy = [|0u8; …; 0u8|] in
         keccak2 136 0x06 [data; data] digest dummy

   The input is duplicated into both SIMD lanes; lane 0's output fills
   [digest] and lane 1's output is discarded into [dummy]. So even
   though the underlying primitive runs in parallel at N=2, the spec
   equivalence we need is single-lane: [digest] == scalar SHA3-256 of
   [data].

   LAYER STRUCTURE (mirrors [EquivImplSpec.Sponge.Portable.API]):

     lemma_keccak2_arm64  : per-lane keccak2 ≡ scalar keccak
       ↓
     lemma_sha*_arm64, lemma_shake*_arm64 : top-level hashers ≡ spec

   [lemma_keccak2_arm64] is ADMITTED — it is the Arm64 counterpart of
   [lemma_absorb_portable] + [lemma_squeeze_portable], requiring
   reasoning over the fold_range in [keccak2] and the per-lane
   NEON bridges [arm64_sc_load_block], [arm64_sc_load_last],
   [arm64_sc_store_block] (the latter three are also admitted and
   constitute the "loop" content).
   ================================================================ *)

#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"

open FStar.Mul
open Core_models

module I = Libcrux_intrinsics.Arm64_extract


(* ================================================================
   LAYER ASSUMPTION: per-lane keccak2 equivalence.

   The two-lane Neon driver [keccak2], at lane l, produces the same
   byte stream as the scalar [Hacspec_sha3.Sponge.keccak] applied to
   input[l].  The proof would compose:
     - per-lane absorb equivalence (via EquivImplSpec.Sponge.Arm64.sc_arm64)
     - per-lane squeeze2 equivalence (ditto)
     - lemma_keccakf1600_arm64 between them.
   ================================================================ *)

assume val lemma_keccak2_arm64
      (rate: usize) (delim: u8)
      (input: t_Array (t_Slice u8) (mk_usize 2))
      (out0 out1: t_Slice u8)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        Libcrux_sha3.Proof_utils.slices_same_len (mk_usize 2) input /\
        Seq.length #u8 out0 < v Core_models.Num.impl_usize__MAX - 200 /\
        Seq.length #u8 out0 == Seq.length #u8 out1)
      (ensures (
        let (r0, r1) =
          Libcrux_sha3.Generic_keccak.Simd128.keccak2
            rate delim input out0 out1 in
        let n : usize = Core_models.Slice.impl__len #u8 out0 in
        r0 == (Hacspec_sha3.Sponge.keccak n rate delim (input.[ mk_usize 0 ]) <: t_Slice u8) /\
        r1 == (Hacspec_sha3.Sponge.keccak n rate delim (input.[ mk_usize 1 ]) <: t_Slice u8)))


(* ================================================================
   PER-HASHER TOP-LEVEL THEOREMS

   Each hasher duplicates [data] into both lanes, so lane 0 of
   [keccak2] gives the scalar hash of [data] — which is exactly
   [Hacspec_sha3.Sha3.sha*_ data].
   ================================================================ *)

let lemma_sha224_arm64 (digest data: t_Slice u8)
  : Lemma
      (requires Seq.length #u8 digest == 28)
      (ensures Libcrux_sha3.Neon.sha224 digest data
               == (Hacspec_sha3.Sha3.sha3_224_ data <: t_Slice u8))
  = let inputs : t_Array (t_Slice u8) (mk_usize 2) =
      let l : list (t_Slice u8) = [ data; data ] in
      FStar.Pervasives.assert_norm (List.Tot.length l == 2);
      Rust_primitives.Hax.array_of_list 2 l in
    let dummy : t_Array u8 (mk_usize 28) =
      Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 28) in
    lemma_keccak2_arm64 (mk_usize 144) (mk_u8 6) inputs digest (dummy <: t_Slice u8)

let lemma_sha256_arm64 (digest data: t_Slice u8)
  : Lemma
      (requires Seq.length #u8 digest == 32)
      (ensures Libcrux_sha3.Neon.sha256 digest data
               == (Hacspec_sha3.Sha3.sha3_256_ data <: t_Slice u8))
  = let inputs : t_Array (t_Slice u8) (mk_usize 2) =
      let l : list (t_Slice u8) = [ data; data ] in
      FStar.Pervasives.assert_norm (List.Tot.length l == 2);
      Rust_primitives.Hax.array_of_list 2 l in
    let dummy : t_Array u8 (mk_usize 32) =
      Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
    lemma_keccak2_arm64 (mk_usize 136) (mk_u8 6) inputs digest (dummy <: t_Slice u8)

let lemma_sha384_arm64 (digest data: t_Slice u8)
  : Lemma
      (requires Seq.length #u8 digest == 48)
      (ensures Libcrux_sha3.Neon.sha384 digest data
               == (Hacspec_sha3.Sha3.sha3_384_ data <: t_Slice u8))
  = let inputs : t_Array (t_Slice u8) (mk_usize 2) =
      let l : list (t_Slice u8) = [ data; data ] in
      FStar.Pervasives.assert_norm (List.Tot.length l == 2);
      Rust_primitives.Hax.array_of_list 2 l in
    let dummy : t_Array u8 (mk_usize 48) =
      Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 48) in
    lemma_keccak2_arm64 (mk_usize 104) (mk_u8 6) inputs digest (dummy <: t_Slice u8)

let lemma_sha512_arm64 (digest data: t_Slice u8)
  : Lemma
      (requires Seq.length #u8 digest == 64)
      (ensures Libcrux_sha3.Neon.sha512 digest data
               == (Hacspec_sha3.Sha3.sha3_512_ data <: t_Slice u8))
  = let inputs : t_Array (t_Slice u8) (mk_usize 2) =
      let l : list (t_Slice u8) = [ data; data ] in
      FStar.Pervasives.assert_norm (List.Tot.length l == 2);
      Rust_primitives.Hax.array_of_list 2 l in
    let dummy : t_Array u8 (mk_usize 64) =
      Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 64) in
    lemma_keccak2_arm64 (mk_usize 72) (mk_u8 6) inputs digest (dummy <: t_Slice u8)

let lemma_shake128_arm64 (v_LEN: usize) (digest: t_Array u8 v_LEN) (data: t_Slice u8)
  : Lemma
      (requires v v_LEN < v Core_models.Num.impl_usize__MAX - 200)
      (ensures
        Libcrux_sha3.Neon.shake128 v_LEN digest data
        == (Hacspec_sha3.Sha3.shake128 v_LEN data <: t_Array u8 v_LEN))
  = let inputs : t_Array (t_Slice u8) (mk_usize 2) =
      let l : list (t_Slice u8) = [ data; data ] in
      FStar.Pervasives.assert_norm (List.Tot.length l == 2);
      Rust_primitives.Hax.array_of_list 2 l in
    let dummy : t_Array u8 v_LEN = Rust_primitives.Hax.repeat (mk_u8 0) v_LEN in
    lemma_keccak2_arm64 (mk_usize 168) (mk_u8 31) inputs
      (digest <: t_Slice u8) (dummy <: t_Slice u8)

let lemma_shake256_arm64 (v_LEN: usize) (digest: t_Array u8 v_LEN) (data: t_Slice u8)
  : Lemma
      (requires v v_LEN < v Core_models.Num.impl_usize__MAX - 200)
      (ensures
        Libcrux_sha3.Neon.shake256 v_LEN digest data
        == (Hacspec_sha3.Sha3.shake256 v_LEN data <: t_Array u8 v_LEN))
  = let inputs : t_Array (t_Slice u8) (mk_usize 2) =
      let l : list (t_Slice u8) = [ data; data ] in
      FStar.Pervasives.assert_norm (List.Tot.length l == 2);
      Rust_primitives.Hax.array_of_list 2 l in
    let dummy : t_Array u8 v_LEN = Rust_primitives.Hax.repeat (mk_u8 0) v_LEN in
    lemma_keccak2_arm64 (mk_usize 136) (mk_u8 31) inputs
      (digest <: t_Slice u8) (dummy <: t_Slice u8)
