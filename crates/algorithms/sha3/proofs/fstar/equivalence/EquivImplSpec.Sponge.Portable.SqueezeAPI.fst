module EquivImplSpec.Sponge.Portable.SqueezeAPI

(* ================================================================
   Portable squeeze driver equivalence.

   Proves: Libcrux_sha3.Generic_keccak.Portable.squeeze ≡
           Hacspec_sha3.Sponge.squeeze

   Factored into its own module to keep the Z3 context for this
   lockstep induction separate from the absorb driver proof in
   [EquivImplSpec.Sponge.Portable.API].

   Strategy: use [Seq.slice out 0 n] prefix equality as the
   lockstep invariant.  A single sequence equation (not a forall)
   keeps Z3's context small across the recursion.
   ================================================================ *)

#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"

open FStar.Mul
open Core_models

module SP = EquivImplSpec.Sponge.Portable
module KP = EquivImplSpec.Keccakf.Portable
module Steps = EquivImplSpec.Sponge.Portable.Steps
module HS = Hacspec_sha3.Sponge

(* Bring Portable typeclass instances into scope. *)
let _ =
  let open Libcrux_sha3.Traits in
  let open Libcrux_sha3.Simd.Portable in
  ()


(* ================================================================
   Step 1: f_squeeze (no keccakf) ≡ squeeze_state.
   ================================================================ *)
#push-options "--z3rlimit 100"
let lemma_squeeze_once_portable
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
        let out' = Libcrux_sha3.Traits.f_squeeze
                     #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
                     #u64
                     #FStar.Tactics.Typeclasses.solve
                     rate ks out start len in
        out' == HS.squeeze_state ks.Libcrux_sha3.Generic_keccak.f_st out start len))
  = let outputs : t_Array (t_Slice u8) (mk_usize 1) =
      let list = [out] in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
      Rust_primitives.Hax.array_of_list 1 list in
    assert (outputs.[ mk_usize 0 ] == out);
    SP.portable_sc_store_block rate ks.Libcrux_sha3.Generic_keccak.f_st
      outputs start len 0;
    KP.lemma_extract_lane_portable_identity ks.Libcrux_sha3.Generic_keccak.f_st
#pop-options


(* ================================================================
   Step 2: prefix-agreement preservation for [squeeze_state].

   Proves (in slice form): if [Seq.slice out1 0 start] equals
   [Seq.slice out2 0 start], then after [squeeze_state state _ start len]
   the prefixes of length [start + len] are equal.

   Uses [squeeze_state]'s pointwise ensures: bytes at [i < start] are
   preserved from input; bytes at [i in [start, start+len)] are derived
   from [state] (same on both sides).
   ================================================================ *)
#push-options "--z3rlimit 300"
let lemma_squeeze_state_grow_slice
      (state: t_Array u64 (mk_usize 25))
      (out1 out2: t_Slice u8)
      (start: usize)
      (len: usize)
  : Lemma
      (requires
        v len <= 200 /\
        v start + v len <= Seq.length #u8 out1 /\
        Seq.length #u8 out1 == Seq.length #u8 out2 /\
        Seq.equal (Seq.slice out1 0 (v start))
                  (Seq.slice out2 0 (v start)))
      (ensures (
        let out1' = HS.squeeze_state state out1 start len in
        let out2' = HS.squeeze_state state out2 start len in
        Seq.length #u8 out1' == Seq.length #u8 out2' /\
        Seq.equal (Seq.slice out1' 0 (v start + v len))
                  (Seq.slice out2' 0 (v start + v len))))
  = let out1' = HS.squeeze_state state out1 start len in
    let out2' = HS.squeeze_state state out2 start len in
    assert (Seq.length #u8 out1' == Seq.length #u8 out1);
    assert (Seq.length #u8 out2' == Seq.length #u8 out2);
    let aux (i: nat{i < v start + v len})
      : Lemma
          (ensures Seq.index out1' i == Seq.index out2' i)
      = let sz_i : usize = sz i in
        assert (v sz_i == i);
        if i < v start then begin
          (* Bytes preserved from input; prefix agreement from hypothesis. *)
          assert (Seq.index out1' i == Seq.index out1 i);
          assert (Seq.index out2' i == Seq.index out2 i);
          assert (Seq.index (Seq.slice out1 0 (v start)) i ==
                  Seq.index (Seq.slice out2 0 (v start)) i);
          assert (Seq.index out1 i ==
                  Seq.index (Seq.slice out1 0 (v start)) i);
          assert (Seq.index out2 i ==
                  Seq.index (Seq.slice out2 0 (v start)) i)
        end
        else ()
    in
    Classical.forall_intro aux;
    (* Convert pointwise to Seq.equal. *)
    Seq.lemma_eq_intro (Seq.slice out1' 0 (v start + v len))
                       (Seq.slice out2' 0 (v start + v len))
#pop-options


(* ================================================================
   Step 2.5: one-step bridge for the middle loop (slice form).
   ================================================================ *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 300"
let lemma_squeeze_middle_one_step
      (rate: usize)
      (k: usize)
      (ks: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
      (spec_state: t_Array u64 (mk_usize 25))
      (impl_out spec_out: t_Slice u8)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v k * v rate + v rate <= Seq.length #u8 impl_out /\
        Seq.length #u8 impl_out == Seq.length #u8 spec_out /\
        ks.Libcrux_sha3.Generic_keccak.f_st == spec_state /\
        Seq.equal (Seq.slice impl_out 0 (v k * v rate))
                  (Seq.slice spec_out 0 (v k * v rate)))
      (ensures (
        let ks' = Libcrux_sha3.Generic_keccak.impl_2__keccakf1600
                    (mk_usize 1) #u64 ks in
        let impl_out' = Libcrux_sha3.Traits.f_squeeze
                          #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
                          #u64
                          #FStar.Tactics.Typeclasses.solve
                          rate ks' impl_out (k *! rate) rate in
        let spec_state' = Hacspec_sha3.Keccak_f.keccak_f spec_state in
        let spec_out'   = HS.squeeze_state spec_state' spec_out
                            (k *! rate) rate in
        Seq.length #u8 impl_out' == Seq.length #u8 impl_out /\
        Seq.length #u8 spec_out' == Seq.length #u8 spec_out /\
        ks'.Libcrux_sha3.Generic_keccak.f_st == spec_state' /\
        Seq.equal (Seq.slice impl_out' 0 (v k * v rate + v rate))
                  (Seq.slice spec_out' 0 (v k * v rate + v rate))))
  = Steps.lemma_squeeze_block_portable rate ks impl_out (k *! rate);
    let spec_state' = Hacspec_sha3.Keccak_f.keccak_f spec_state in
    lemma_squeeze_state_grow_slice spec_state' impl_out spec_out
      (k *! rate) rate
#pop-options


(* ================================================================
   Step 3: middle-loop equivalence (lockstep induction).

   NOTE: This is the inductive driver over the middle fold_range.
   The per-step bridge [lemma_squeeze_middle_one_step] (above) is
   proved; the induction skeleton itself is currently left as an
   [assume val] because F*'s Z3 backend times out resolving the
   extractor's inline-lambda subtyping obligations inside the
   recursive call (reported as 258 cascading Error 19s).

   Status of helpers that ARE proved in this module:
     - lemma_squeeze_once_portable          (f_squeeze ≡ squeeze_state)
     - lemma_squeeze_state_grow_slice       (pointwise → Seq.equal)
     - lemma_squeeze_middle_one_step        (one middle iteration)
   These are the re-usable building blocks for a future proof; once
   closed, [lemma_squeeze_portable] can be derived by induction.
   ================================================================ *)
assume val lemma_squeeze_portable_middle
      (rate: usize)
      (output_blocks: usize)
      (k: usize)
      (ks: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
      (spec_state: t_Array u64 (mk_usize 25))
      (impl_out spec_out: t_Slice u8)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v k >= 1 /\ v k <= v output_blocks /\
        v output_blocks * v rate <= Seq.length #u8 impl_out /\
        Seq.length #u8 impl_out == Seq.length #u8 spec_out /\
        ks.Libcrux_sha3.Generic_keccak.f_st == spec_state /\
        Seq.equal (Seq.slice impl_out 0 (v k * v rate))
                  (Seq.slice spec_out 0 (v k * v rate)))
      (ensures (
        let output_len : usize = Core_models.Slice.impl__len #u8 impl_out in
        let (impl_out_final, ks_final) =
          Rust_primitives.Hax.Folds.fold_range k output_blocks
            (fun temp_0_ temp_1_ ->
                let (output: t_Slice u8), (s: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64) = temp_0_ in
                let _:usize = temp_1_ in
                (Core_models.Slice.impl__len #u8 output <: usize) =. output_len <: bool)
            (impl_out, ks <: (t_Slice u8 & Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64))
            (fun temp_0_ i ->
                let (output: t_Slice u8), (s: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64) = temp_0_ in
                let i:usize = i in
                let _:Prims.unit =
                  Libcrux_sha3.Proof_utils.Lemmas.lemma_mul_succ_le i output_blocks rate
                in
                let s:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 =
                  Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 (mk_usize 1) #u64 s
                in
                let output:t_Slice u8 =
                  Libcrux_sha3.Traits.f_squeeze #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
                    #u64
                    #FStar.Tactics.Typeclasses.solve
                    rate s output (i *! rate <: usize) rate in
                output, s <: (t_Slice u8 & Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)) in
        let (spec_out_final, spec_state_final) =
          EquivImplSpec.Sponge.Generic.Squeeze.spec_squeeze_loop
            spec_state spec_out rate k output_blocks in
        Seq.length #u8 impl_out_final == Seq.length #u8 spec_out_final /\
        ks_final.Libcrux_sha3.Generic_keccak.f_st == spec_state_final /\
        Seq.equal (Seq.slice impl_out_final 0 (v output_blocks * v rate))
                  (Seq.slice spec_out_final 0 (v output_blocks * v rate))))


(* ================================================================
   Step 4: full squeeze driver equivalence.

   NOTE: The full driver is also left as [assume val] for now,
   because its proof depends on [lemma_squeeze_portable_middle]
   (currently assumed) and additionally involves bridging the
   middle-loop result to the final-slice equality through a
   partial-block tail.  The surrounding structure is proved: the
   peel-off of the first block reduces to [lemma_squeeze_once_portable]
   and [lemma_squeeze_state_grow_slice], both closed above.
   ================================================================ *)
assume val lemma_squeeze_portable
      (rate: usize)
      (state: t_Array u64 (mk_usize 25))
      (output: t_Slice u8)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        Seq.length #u8 output < v Core_models.Num.impl_usize__MAX - 200)
      (ensures (
        let ks : Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 =
          { Libcrux_sha3.Generic_keccak.f_st = state } in
        let output_len : usize = Core_models.Slice.impl__len #u8 output in
        Libcrux_sha3.Generic_keccak.Portable.squeeze rate ks output
        ==
        (Hacspec_sha3.Sponge.squeeze output_len state rate <: t_Slice u8)))
