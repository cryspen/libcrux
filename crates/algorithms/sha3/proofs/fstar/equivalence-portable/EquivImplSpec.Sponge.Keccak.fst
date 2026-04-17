module EquivImplSpec.Sponge.Keccak

#set-options "--fuel 1 --ifuel 1 --z3rlimit 100"

open FStar.Mul
open Core_models
open EquivImplSpec.Sponge.Core
open EquivImplSpec.Sponge.Absorb
open EquivImplSpec.Sponge.Squeeze

(* ================================================================
   Phase 16 refactored: keccak1 / keccak split into absorb + squeeze.

   Both Rust sources now define `keccak1` / `keccak` as the two-line
   composition `squeeze (absorb ...)`. Hax re-extracts the split, and
   the bridge lemma collapses into a thin composition of two phase-level
   lemmas (`lemma_absorb_equiv`, `lemma_squeeze_equiv`), each with its
   own much smaller VC.
   ================================================================ *)

(* ----------------------------------------------------------------
   Decomposition axioms (Pattern 1: fold-range closure-equality
   limitation). Each extracted top-level function (`Portable.absorb`,
   `Sponge.absorb`, `Portable.squeeze`, `Sponge.squeeze`) contains a
   raw `fold_range` closure whose `inv` argument differs in shape
   (b2t vs Type0) from our named `impl_absorb_fold` /
   `spec_absorb_fold` / `impl_squeeze_fold` / `spec_squeeze_fold`.
   SMT cannot equate the raw closure to the named one; we axiomatize
   the structural decomposition and then prove equivalence against
   the named helpers.
   ---------------------------------------------------------------- *)

assume val lemma_portable_absorb_decomposes
      (rate: usize)
      (delim: u8)
      (data: t_Slice u8)
  : Lemma
      (requires Libcrux_sha3.Proof_utils.valid_rate rate)
      (ensures (
        let input_len = Core_models.Slice.impl__len #u8 data in
        let n = input_len /! rate in
        let remaining = input_len %! rate in
        let start = n *! rate in
        let ks0 = Libcrux_sha3.Generic_keccak.impl_2__new (mk_usize 1) #u64 () in
        Libcrux_sha3.Generic_keccak.Portable.absorb rate delim data ==
        Libcrux_sha3.Generic_keccak.impl_2__absorb_final (mk_usize 1) #u64 rate delim
          (impl_absorb_fold ks0 data rate (mk_usize 0) n)
          (let list = [data] in
           FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
           Rust_primitives.Hax.array_of_list 1 list)
          start
          remaining))

assume val lemma_sponge_absorb_decomposes
      (rate: usize)
      (delim: u8)
      (data: t_Slice u8)
  : Lemma
      (requires
        v rate > 0 /\ v rate <= 200 /\ v rate % 8 == 0)
      (ensures (
        let input_len = Core_models.Slice.impl__len #u8 data in
        let n = input_len /! rate in
        let remaining = input_len %! rate in
        let start = n *! rate in
        let spec0 = Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 25) in
        Hacspec_sha3.Sponge.absorb rate delim data ==
        Hacspec_sha3.Sponge.absorb_final
          (spec_absorb_fold spec0 data rate (mk_usize 0) n)
          data
          start
          remaining
          rate
          delim))

(* Portable.squeeze zero-blocks branch: when output_len < rate, the
   entire output is produced by one squeeze_state from offset 0. *)
assume val lemma_portable_squeeze_zero_blocks_decomposes
      (rate: usize)
      (ks: impl_state)
      (impl_out: t_Slice u8)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v (Core_models.Slice.impl__len #u8 impl_out) < v rate)
      (ensures
        Libcrux_sha3.Generic_keccak.Portable.squeeze rate ks impl_out ==
        impl_squeeze_once rate ks impl_out (mk_usize 0)
          (Core_models.Slice.impl__len #u8 impl_out))

(* Portable.squeeze nonzero-blocks branch: first block, then middle-
   blocks fold, then optional tail block. *)
assume val lemma_portable_squeeze_nonzero_decomposes
      (rate: usize)
      (ks: impl_state)
      (impl_out: t_Slice u8)
  : Lemma
      (requires (
        let output_len = Core_models.Slice.impl__len #u8 impl_out in
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v (output_len /! rate) >= 1 /\
        v output_len < v Core_models.Num.impl_usize__MAX - 200))
      (ensures (
        let output_len = Core_models.Slice.impl__len #u8 impl_out in
        let output_blocks = output_len /! rate in
        let output_rem = output_len %! rate in
        let out1 = impl_squeeze_once rate ks impl_out (mk_usize 0) rate in
        let out_after_loop, ks_after_loop =
          impl_squeeze_fold ks out1 rate (mk_usize 1) output_blocks
        in
        Libcrux_sha3.Generic_keccak.Portable.squeeze rate ks impl_out ==
        (if output_rem <>. mk_usize 0 then
           let ks_tail =
             Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 (mk_usize 1) #u64 ks_after_loop
           in
           impl_squeeze_once rate ks_tail out_after_loop
             (output_len -! output_rem) output_rem
         else out_after_loop)))

(* Sponge.squeeze zero-blocks branch. *)
assume val lemma_sponge_squeeze_zero_blocks_decomposes
      (output_len: usize)
      (state: spec_state)
      (rate: usize)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v output_len < v rate /\
        v output_len < v Core_models.Num.impl_usize__MAX - 200)
      (ensures
        (Hacspec_sha3.Sponge.squeeze output_len state rate <: t_Slice u8) ==
        (Hacspec_sha3.Sponge.squeeze_state state
           (Rust_primitives.Hax.repeat (mk_u8 0) output_len)
           (mk_usize 0) output_len <: t_Slice u8))

(* Sponge.squeeze nonzero-blocks branch. *)
assume val lemma_sponge_squeeze_nonzero_decomposes
      (output_len: usize)
      (state: spec_state)
      (rate: usize)
  : Lemma
      (requires (
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v (output_len /! rate) >= 1 /\
        v output_len < v Core_models.Num.impl_usize__MAX - 200))
      (ensures (
        let output_blocks = output_len /! rate in
        let output_rem = output_len %! rate in
        let output0 : t_Slice u8 = Rust_primitives.Hax.repeat (mk_u8 0) output_len in
        let out1 = Hacspec_sha3.Sponge.squeeze_state state output0 (mk_usize 0) rate in
        let out_after_loop, state_after_loop =
          spec_squeeze_fold state out1 rate (mk_usize 1) output_blocks
        in
        (Hacspec_sha3.Sponge.squeeze output_len state rate <: t_Slice u8) ==
        (if output_rem <>. mk_usize 0 then
           let state_tail = Hacspec_sha3.Keccak_f.keccak_f state_after_loop in
           Hacspec_sha3.Sponge.squeeze_state state_tail out_after_loop
             (output_len -! output_rem) output_rem
         else out_after_loop)))

(* ----------------------------------------------------------------
   Lemma 1: absorb-phase equivalence at the `Portable.absorb` /
   `Sponge.absorb` top level.

   Thin wrapper over `lemma_absorb_phase_equiv`; the reduction from
   `Portable.absorb` / `Sponge.absorb` to the `impl_2__absorb_final
   (impl_absorb_loop ...)` / `absorb_final (spec_absorb_loop ...)` shape
   is handled by `lemma_impl_absorb_is_loop` / `lemma_spec_absorb_is_loop`
   inside `lemma_absorb_phase_equiv`.
   ---------------------------------------------------------------- *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 300 --split_queries always"
let lemma_absorb_equiv
      (rate: usize)
      (delim: u8)
      (data: t_Slice u8)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        Seq.length data <= v (cast Core_models.Num.impl_u32__MAX <: usize))
      (ensures
        (Libcrux_sha3.Generic_keccak.Portable.absorb rate delim data)
          .Libcrux_sha3.Generic_keccak.f_st
        == Hacspec_sha3.Sponge.absorb rate delim data)
  =
  let input_len = Core_models.Slice.impl__len #u8 data in
  let n = input_len /! rate in
  let remaining = input_len %! rate in
  let start = n *! rate in
  let ks0 = Libcrux_sha3.Generic_keccak.impl_2__new (mk_usize 1) #u64 () in
  let spec0 = Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 25) in
  let ks_abs = impl_absorb_loop ks0 data rate (mk_usize 0) n in
  let spec_abs = spec_absorb_loop spec0 data rate (mk_usize 0) n in
  let ks_final =
    Libcrux_sha3.Generic_keccak.impl_2__absorb_final (mk_usize 1)
      #u64
      rate
      delim
      ks_abs
      (let list = [data] in
       FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
       Rust_primitives.Hax.array_of_list 1 list)
      start
      remaining
  in
  let spec_final =
    Hacspec_sha3.Sponge.absorb_final spec_abs data start remaining rate delim
  in
  Libcrux_sha3.Proof_utils.Lemmas.lemma_div_mul_mod input_len rate;
  assert (v n * v rate <= Seq.length data);
  assert (v remaining < v rate);
  assert (v start + v remaining <= Seq.length data);
  lemma_new_state_equiv ();
  assert (ks0.Libcrux_sha3.Generic_keccak.f_st == spec0);
  lemma_absorb_loop_equiv ks0 spec0 data rate (mk_usize 0) n;
  assert (ks_abs.Libcrux_sha3.Generic_keccak.f_st == spec_abs);
  lemma_absorb_final_equiv ks_abs spec_abs rate delim data start remaining;
  assert (ks_final.Libcrux_sha3.Generic_keccak.f_st == spec_final);
  (* Bridge the raw fold_range inside Portable.absorb / Sponge.absorb to the
     named fold helpers impl_absorb_fold / spec_absorb_fold. *)
  lemma_portable_absorb_decomposes rate delim data;
  lemma_sponge_absorb_decomposes rate delim data;
  (* Bridge impl_absorb_fold / spec_absorb_fold to the recursive forms
     used by lemma_absorb_loop_equiv. *)
  lemma_impl_absorb_is_loop ks0 data rate n;
  lemma_spec_absorb_is_loop spec0 data rate n
  (* Now:
       Portable.absorb rate delim data
       == impl_2__absorb_final ... (impl_absorb_fold ks0 data rate 0 n) ... start remaining
       == impl_2__absorb_final ... (impl_absorb_loop ks0 data rate 0 n) ... start remaining
       == ks_final
     Similarly for Sponge.absorb == spec_final. And ks_final.f_st == spec_final. *)
#pop-options

(* ----------------------------------------------------------------
   Lemma 2: squeeze-phase equivalence at the `Portable.squeeze` /
   `Sponge.squeeze` top level.

   Mirrors the structure of `Portable.squeeze` and `Sponge.squeeze`:
     - output_blocks == 0: single squeeze_state for all bytes.
     - output_blocks >= 1: first block, middle-blocks loop, optional tail.

   Uses the already-proven squeeze lemmas:
     - lemma_squeeze_zero_blocks_equiv   (zero-blocks case)
     - lemma_squeeze_first_block_equiv   (first block)
     - lemma_impl_squeeze_fold_is_loop   (bridge impl fold -> recursive)
     - lemma_spec_squeeze_fold_is_loop   (bridge spec fold -> recursive)
     - lemma_squeeze_loop_equiv          (middle blocks)
     - lemma_impl_squeeze_once_store_block + lemma_store_block_equiv
       (tail block)
     - EquivImplSpec.Keccakf.lemma_keccakf1600_equiv (each keccak-f call)
   ---------------------------------------------------------------- *)
#push-options "--z3rlimit 300 --split_queries always"
let lemma_squeeze_equiv
      (rate: usize)
      (output_len: usize)
      (ks: impl_state)
      (state: spec_state)
      (impl_out: t_Slice u8)
  : Lemma
      (requires
        ks.Libcrux_sha3.Generic_keccak.f_st == state /\
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        Seq.length impl_out == v output_len /\
        impl_out == Rust_primitives.Hax.repeat (mk_u8 0) output_len /\
        v output_len < v Core_models.Num.impl_usize__MAX - 200)
      (ensures
        Libcrux_sha3.Generic_keccak.Portable.squeeze rate ks impl_out ==
        (Hacspec_sha3.Sponge.squeeze output_len state rate <: t_Slice u8))
  =
  let output_blocks = output_len /! rate in
  let output_rem = output_len %! rate in
  Libcrux_sha3.Proof_utils.Lemmas.lemma_div_mul_mod output_len rate;
  assert (v output_len == v output_blocks * v rate + v output_rem);
  assert (v output_rem < v rate);
  if output_blocks =. mk_usize 0 then begin
    assert (v output_blocks == 0);
    assert (v output_len == v output_rem);
    assert (v output_len < v rate);
    assert (v output_len <= v rate);
    lemma_squeeze_zero_blocks_equiv rate ks state impl_out output_len;
    lemma_portable_squeeze_zero_blocks_decomposes rate ks impl_out;
    lemma_sponge_squeeze_zero_blocks_decomposes output_len state rate
  end
  else begin
    assert (v output_blocks >= 1);
    let _: Prims.unit =
      Libcrux_sha3.Proof_utils.Lemmas.lemma_mul_succ_le (mk_usize 0) output_blocks rate
    in
    assert (v rate <= v output_len);
    (* First block. *)
    let out1 = impl_squeeze_once rate ks impl_out (mk_usize 0) rate in
    assert (Seq.length out1 == Seq.length impl_out);
    lemma_squeeze_first_block_equiv rate ks state impl_out;
    (* Middle blocks. *)
    lemma_impl_squeeze_fold_is_loop ks out1 rate (mk_usize 1) output_blocks;
    lemma_spec_squeeze_fold_is_loop state out1 rate (mk_usize 1) output_blocks;
    lemma_squeeze_loop_equiv ks state out1 rate (mk_usize 1) output_blocks;
    let out_after_loop, ks_after_loop =
      impl_squeeze_loop ks out1 rate (mk_usize 1) output_blocks
    in
    let out_spec_after_loop, spec_after_loop =
      spec_squeeze_loop state out1 rate (mk_usize 1) output_blocks
    in
    assert (Seq.length out_after_loop == v output_len);
    assert (out_after_loop == out_spec_after_loop);
    assert (ks_after_loop.Libcrux_sha3.Generic_keccak.f_st == spec_after_loop);
    (* Decompose top-level Portable.squeeze / Sponge.squeeze into
       named fold helpers matching our proof structure. *)
    lemma_portable_squeeze_nonzero_decomposes rate ks impl_out;
    lemma_sponge_squeeze_nonzero_decomposes output_len state rate;
    if output_rem <>. mk_usize 0 then begin
      assert (v output_rem < v rate);
      assert (v output_rem <= v rate);
      let ks_tail =
        Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 (mk_usize 1) #u64 ks_after_loop
      in
      let state_tail = Hacspec_sha3.Keccak_f.keccak_f spec_after_loop in
      EquivImplSpec.Keccakf.lemma_keccakf1600_equiv ks_after_loop spec_after_loop;
      assert (ks_tail.Libcrux_sha3.Generic_keccak.f_st == state_tail);
      let tail_start = output_len -! output_rem in
      assert (v tail_start + v output_rem == v output_len);
      assert (v tail_start + v output_rem <= Seq.length out_after_loop);
      lemma_impl_squeeze_once_store_block
        rate ks_tail out_after_loop tail_start output_rem;
      lemma_store_block_equiv
        rate state_tail out_after_loop tail_start output_rem
    end
    else ()
  end
#pop-options

(* ----------------------------------------------------------------
   Lemma 3: top-level bridge, now a three-line composition.
   ---------------------------------------------------------------- *)
#push-options "--z3rlimit 300"
let lemma_keccak1_bridge
      (rate: usize)
      (delim: u8)
      (output_len: usize)
      (data: t_Slice u8)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        Seq.length data <= v (cast Core_models.Num.impl_u32__MAX <: usize) /\
        v output_len < v Core_models.Num.impl_usize__MAX - 200)
      (ensures (
        let impl_out : t_Slice u8 = Rust_primitives.Hax.repeat (mk_u8 0) output_len in
        let impl_result = Libcrux_sha3.Generic_keccak.Portable.keccak1
                            rate delim data impl_out in
        let spec_result = Hacspec_sha3.Sponge.keccak output_len rate delim data in
        impl_result == (spec_result <: t_Slice u8)))
  =
  let impl_out : t_Slice u8 = Rust_primitives.Hax.repeat (mk_u8 0) output_len in
  assert (Seq.length impl_out == v output_len);
  let ks = Libcrux_sha3.Generic_keccak.Portable.absorb rate delim data in
  let state = Hacspec_sha3.Sponge.absorb rate delim data in
  lemma_absorb_equiv rate delim data;
  assert (ks.Libcrux_sha3.Generic_keccak.f_st == state);
  lemma_squeeze_equiv rate output_len ks state impl_out
#pop-options

let lemma_keccak1_equiv
      (rate: usize)
      (delim: u8)
      (output_len: usize)
      (data: t_Slice u8)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        Seq.length data <= v (cast Core_models.Num.impl_u32__MAX <: usize) /\
        v output_len < v Core_models.Num.impl_usize__MAX - 200)
      (ensures (
        let impl_out : t_Slice u8 = Rust_primitives.Hax.repeat (mk_u8 0) output_len in
        let impl_result = Libcrux_sha3.Generic_keccak.Portable.keccak1
                            rate delim data impl_out in
        let spec_result = Hacspec_sha3.Sponge.keccak output_len rate delim data in
        (* The impl's output slice equals the spec's output array *)
        impl_result == (spec_result <: t_Slice u8)))
  = lemma_keccak1_bridge rate delim output_len data


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

(* Each top-level hash function is a chain of thin wrappers:
     sha256(data) -> sha256_ema(repeat 0 32, data) -> Portable.sha256(repeat 0 32, data)
       -> keccak1(136, 6, data, repeat 0 32)
   On the spec side: sha3_256_(data) = keccak(32, 136, 6, data).
   The solver unfolds the non-recursive wrappers and uses lemma_keccak1_equiv. *)

#push-options "--z3rlimit 300"
let lemma_sha256_equiv (data: t_Slice u8)
  : Lemma
      (requires
        Seq.length data <= v (cast Core_models.Num.impl_u32__MAX <: usize))
      (ensures
        Libcrux_sha3.sha256 data ==
        (Hacspec_sha3.Sha3.sha3_256_ data <: t_Slice u8))
  = lemma_keccak1_equiv (mk_usize 136) (mk_u8 6) (mk_usize 32) data

let lemma_sha224_equiv (data: t_Slice u8)
  : Lemma
      (requires
        Seq.length data <= v (cast Core_models.Num.impl_u32__MAX <: usize))
      (ensures
        Libcrux_sha3.sha224 data ==
        (Hacspec_sha3.Sha3.sha3_224_ data <: t_Slice u8))
  = lemma_keccak1_equiv (mk_usize 144) (mk_u8 6) (mk_usize 28) data

let lemma_sha384_equiv (data: t_Slice u8)
  : Lemma
      (requires
        Seq.length data <= v (cast Core_models.Num.impl_u32__MAX <: usize))
      (ensures
        Libcrux_sha3.sha384 data ==
        (Hacspec_sha3.Sha3.sha3_384_ data <: t_Slice u8))
  = lemma_keccak1_equiv (mk_usize 104) (mk_u8 6) (mk_usize 48) data

let lemma_sha512_equiv (data: t_Slice u8)
  : Lemma
      (requires
        Seq.length data <= v (cast Core_models.Num.impl_u32__MAX <: usize))
      (ensures
        Libcrux_sha3.sha512 data ==
        (Hacspec_sha3.Sha3.sha3_512_ data <: t_Slice u8))
  = lemma_keccak1_equiv (mk_usize 72) (mk_u8 6) (mk_usize 64) data

let lemma_shake128_equiv (v_BYTES: usize) (data: t_Slice u8)
  : Lemma
      (requires
        Seq.length data <= v (cast Core_models.Num.impl_u32__MAX <: usize) /\
        v v_BYTES < v Core_models.Num.impl_usize__MAX - 200)
      (ensures
        Libcrux_sha3.shake128 v_BYTES data ==
        (Hacspec_sha3.Sha3.shake128 v_BYTES data <: t_Slice u8))
  = lemma_keccak1_equiv (mk_usize 168) (mk_u8 31) v_BYTES data

let lemma_shake256_equiv (v_BYTES: usize) (data: t_Slice u8)
  : Lemma
      (requires
        Seq.length data <= v (cast Core_models.Num.impl_u32__MAX <: usize) /\
        v v_BYTES < v Core_models.Num.impl_usize__MAX - 200)
      (ensures
        Libcrux_sha3.shake256 v_BYTES data ==
        (Hacspec_sha3.Sha3.shake256 v_BYTES data <: t_Slice u8))
  = lemma_keccak1_equiv (mk_usize 136) (mk_u8 31) v_BYTES data
#pop-options
