module EquivImplSpec.Sponge.Generic.Absorb

(* ================================================================
   Generic absorb-phase proof for any KeccakItem backend.

   Given a `lane_correctness` and `sponge_correctness` record, proves
   per-lane commutativity of the absorb phase:

     extract_lane(impl_absorb_loop(ks, inputs, rate, 0, n).f_st, l)
     == spec_absorb_loop(extract_lane(ks.f_st, l), inputs[l], rate, 0, n)

   And similarly for absorb_final.
   ================================================================ *)

#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"

open FStar.Mul
open Core_models
open FStar.Tactics.Typeclasses

module G = EquivImplSpec.Keccakf.Generic
module SC = EquivImplSpec.Sponge.Generic.Core

(* Bring typeclass instances into scope *)
let _ =
  let open Libcrux_sha3.Traits in
  let open Libcrux_sha3.Simd.Portable in
  ()


(* ================================================================
   Spec-side recursive absorb loop (scalar, on t_Array u64 25).
   Identical across all backends — operates on a single lane's data.
   ================================================================ *)

let rec spec_absorb_loop
      (state: SC.spec_state)
      (message: t_Slice u8)
      (rate: usize)
      (i n: usize)
  : Pure SC.spec_state
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


(* ================================================================
   Impl-side recursive absorb loop (generic N, on t_KeccakState v_N v_T).
   Mirrors the fold_range body of the extracted absorb function.
   ================================================================ *)

let rec impl_absorb_loop_generic
      (v_N: usize) (#v_T: Type0)
      {| ki: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      {| ab: Libcrux_sha3.Traits.t_Absorb
               (Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T) v_N |}
      (ks: Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T)
      (inputs: t_Array (t_Slice u8) v_N)
      (rate: usize)
      (i n: usize)
  : Pure (Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T)
      (requires
        v v_N > 0 /\
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v i <= v n /\
        v n * v rate <= Seq.length #u8 (inputs.[ mk_usize 0 ]) /\
        Libcrux_sha3.Proof_utils.slices_same_len v_N inputs)
      (ensures fun _ -> True)
      (decreases (v n - v i))
  = if i =. n then ks
    else
      let start = i *! rate in
      let ks' = Libcrux_sha3.Generic_keccak.impl_2__absorb_block v_N #v_T rate
                  ks inputs start in
      impl_absorb_loop_generic v_N ks' inputs rate (i +! mk_usize 1) n


(* ================================================================
   Per-step lemma: absorb_block commutes with extract_lane.

   Proof: unfold impl_2__absorb_block = f_load_block then keccakf1600.
   Apply sc.sc_load_block for the load step.
   Apply G.lemma_keccakf1600_to_spec for the keccakf step.
   Combine with spec absorb_block = keccak_f ∘ xor_block_into_state.
   ================================================================ *)

#push-options "--fuel 1 --z3rlimit 200"
let lemma_absorb_block_generic
      (v_N: usize) (#v_T: Type0)
      {| ki: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      {| ab: Libcrux_sha3.Traits.t_Absorb
               (Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T) v_N |}
      (lc: G.lane_correctness v_N #v_T)
      (sc: SC.sponge_correctness v_N #v_T lc)
      (ks: Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T)
      (inputs: t_Array (t_Slice u8) v_N)
      (rate: usize)
      (start: usize)
      (l: nat{l < v v_N})
  : Lemma
      (requires
        v v_N > 0 /\
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v start + v rate <= Seq.length #u8 (inputs.[ mk_usize 0 ]) /\
        Libcrux_sha3.Proof_utils.slices_same_len v_N inputs)
      (ensures (
        let block_l = inputs.[ mk_usize l ].[ {
            Core_models.Ops.Range.f_start = start;
            Core_models.Ops.Range.f_end   = start +! rate } <:
          Core_models.Ops.Range.t_Range usize ] in
        G.extract_lane v_N lc
          (Libcrux_sha3.Generic_keccak.impl_2__absorb_block v_N #v_T rate
             ks inputs start)
            .Libcrux_sha3.Generic_keccak.f_st
          l
        ==
        Hacspec_sha3.Sponge.absorb_block
          (G.extract_lane v_N lc ks.Libcrux_sha3.Generic_keccak.f_st l)
          block_l
          rate))
  =
  (* Step 1: f_load_block commutes with extract_lane *)
  sc.sc_load_block rate ks.Libcrux_sha3.Generic_keccak.f_st inputs start l;
  (* Step 2: keccakf1600 commutes with extract_lane *)
  let loaded_ks =
    Libcrux_sha3.Traits.f_load_block #_ #_ #ab rate ks inputs start in
  G.lemma_keccakf1600_to_spec v_N lc loaded_ks l
#pop-options


(* ================================================================
   Per-step lemma: absorb_final commutes with extract_lane.

   Proof: same pattern — sc.sc_load_last then G.lemma_keccakf1600_to_spec.
   ================================================================ *)

#push-options "--fuel 1 --z3rlimit 200"
let lemma_absorb_final_generic
      (v_N: usize) (#v_T: Type0)
      {| ki: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      {| ab: Libcrux_sha3.Traits.t_Absorb
               (Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T) v_N |}
      (lc: G.lane_correctness v_N #v_T)
      (sc: SC.sponge_correctness v_N #v_T lc)
      (ks: Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T)
      (inputs: t_Array (t_Slice u8) v_N)
      (rate: usize)
      (delim: u8)
      (start remaining: usize)
      (l: nat{l < v v_N})
  : Lemma
      (requires
        v v_N > 0 /\
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v remaining < v rate /\
        v start + v remaining <= Seq.length #u8 (inputs.[ mk_usize 0 ]) /\
        Libcrux_sha3.Proof_utils.slices_same_len v_N inputs)
      (ensures
        G.extract_lane v_N lc
          (Libcrux_sha3.Generic_keccak.impl_2__absorb_final v_N #v_T rate delim
             ks inputs start remaining)
            .Libcrux_sha3.Generic_keccak.f_st
          l
        ==
        Hacspec_sha3.Sponge.absorb_final
          (G.extract_lane v_N lc ks.Libcrux_sha3.Generic_keccak.f_st l)
          (inputs.[ mk_usize l ] <: t_Slice u8)
          start remaining rate delim)
  =
  (* Step 1: f_load_last commutes with extract_lane *)
  sc.sc_load_last rate delim ks.Libcrux_sha3.Generic_keccak.f_st inputs start remaining l;
  (* Step 2: keccakf1600 commutes with extract_lane *)
  let loaded_ks =
    Libcrux_sha3.Traits.f_load_last #_ #_ #ab rate delim ks inputs start remaining in
  G.lemma_keccakf1600_to_spec v_N lc loaded_ks l
#pop-options


(* ================================================================
   Inductive equivalence: impl_absorb_loop_generic commutes with
   spec_absorb_loop via extract_lane.

   At each step: apply lemma_absorb_block_generic, then recurse.
   Follows the lockstep induction pattern from EquivImplSpec.Keccakf.Generic.
   ================================================================ *)

#push-options "--fuel 1 --z3rlimit 200"
let rec lemma_absorb_loop_generic
      (v_N: usize) (#v_T: Type0)
      {| ki: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      {| ab: Libcrux_sha3.Traits.t_Absorb
               (Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T) v_N |}
      (lc: G.lane_correctness v_N #v_T)
      (sc: SC.sponge_correctness v_N #v_T lc)
      (ks: Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T)
      (inputs: t_Array (t_Slice u8) v_N)
      (rate: usize)
      (i n: usize)
      (l: nat{l < v v_N})
  : Lemma
      (requires
        v v_N > 0 /\
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v i <= v n /\
        v n * v rate <= Seq.length #u8 (inputs.[ mk_usize 0 ]) /\
        Libcrux_sha3.Proof_utils.slices_same_len v_N inputs)
      (ensures
        G.extract_lane v_N lc
          (impl_absorb_loop_generic v_N ks inputs rate i n)
            .Libcrux_sha3.Generic_keccak.f_st
          l
        ==
        spec_absorb_loop
          (G.extract_lane v_N lc ks.Libcrux_sha3.Generic_keccak.f_st l)
          (inputs.[ mk_usize l ] <: t_Slice u8)
          rate i n)
      (decreases (v n - v i))
  =
  if i =. n then ()
  else begin
    let start = i *! rate in
    lemma_absorb_block_generic v_N lc sc ks inputs rate start l;
    let ks' = Libcrux_sha3.Generic_keccak.impl_2__absorb_block v_N #v_T rate
                ks inputs start in
    lemma_absorb_loop_generic v_N lc sc ks' inputs rate (i +! mk_usize 1) n l
  end
#pop-options


(* ================================================================
   New-state equivalence: extract_lane of the zero state is the
   scalar zero state.
   ================================================================ *)

#push-options "--fuel 1 --z3rlimit 200"
let lemma_new_state_generic
      (v_N: usize) (#v_T: Type0)
      {| ki: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      (lc: G.lane_correctness v_N #v_T)
      (l: nat{l < v v_N})
  : Lemma
      (G.extract_lane v_N lc
        (Libcrux_sha3.Generic_keccak.impl_2__new v_N #v_T ())
          .Libcrux_sha3.Generic_keccak.f_st
        l
      ==
      Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 25))
  =
  let st = (Libcrux_sha3.Generic_keccak.impl_2__new v_N #v_T ())
             .Libcrux_sha3.Generic_keccak.f_st in
  let spec_st = Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 25) in
  let extracted = G.extract_lane v_N lc st l in
  (* Pointwise: extract_lane(st, l).[k] == lc.lane(st.[k], l) == 0 *)
  let aux (k: nat{k < 25}) : Lemma (Seq.index extracted k == Seq.index spec_st k)
    = G.lemma_extract_lane_index v_N lc st l (mk_usize k);
      lc.lc_zero l
  in
  FStar.Classical.forall_intro aux;
  assert (Seq.equal extracted spec_st)
#pop-options


(* ================================================================
   Full absorb-phase composition: loop + final step.

   extract_lane(absorb_final(absorb_loop(new(), inputs, rate, 0, n), ...).f_st, l)
   == Sponge.absorb_final(spec_absorb_loop(zeros, inputs[l], rate, 0, n), ...)
   ================================================================ *)

#push-options "--fuel 0 --z3rlimit 200"
let lemma_absorb_phase_generic
      (v_N: usize) (#v_T: Type0)
      {| ki: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      {| ab: Libcrux_sha3.Traits.t_Absorb
               (Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T) v_N |}
      (lc: G.lane_correctness v_N #v_T)
      (sc: SC.sponge_correctness v_N #v_T lc)
      (inputs: t_Array (t_Slice u8) v_N)
      (rate: usize)
      (delim: u8)
      (l: nat{l < v v_N})
  : Lemma
      (requires
        v v_N > 0 /\
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        Seq.length #u8 (inputs.[ mk_usize 0 ]) <= v (cast Core_models.Num.impl_u32__MAX <: usize) /\
        Libcrux_sha3.Proof_utils.slices_same_len v_N inputs)
      (ensures (
        let input_len = Core_models.Slice.impl__len #u8 (inputs.[ mk_usize 0 ]) in
        let n = input_len /! rate in
        let remaining = input_len %! rate in
        let start = n *! rate in
        let ks0 = Libcrux_sha3.Generic_keccak.impl_2__new v_N #v_T () in
        let spec0 = Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 25) in
        let ks_abs = impl_absorb_loop_generic v_N ks0 inputs rate (mk_usize 0) n in
        let ks_final = Libcrux_sha3.Generic_keccak.impl_2__absorb_final v_N #v_T
                         rate delim ks_abs inputs start remaining in
        G.extract_lane v_N lc ks_final.Libcrux_sha3.Generic_keccak.f_st l
        ==
        Hacspec_sha3.Sponge.absorb_final
          (spec_absorb_loop spec0 (inputs.[ mk_usize l ] <: t_Slice u8)
             rate (mk_usize 0) n)
          (inputs.[ mk_usize l ] <: t_Slice u8)
          start remaining rate delim))
  =
  let input_len = Core_models.Slice.impl__len #u8 (inputs.[ mk_usize 0 ]) in
  let n = input_len /! rate in
  let remaining = input_len %! rate in
  let start = n *! rate in
  let ks0 = Libcrux_sha3.Generic_keccak.impl_2__new v_N #v_T () in
  let spec0 = Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 25) in
  Libcrux_sha3.Proof_utils.Lemmas.lemma_div_mul_mod input_len rate;
  lemma_new_state_generic v_N lc l;
  lemma_absorb_loop_generic v_N lc sc ks0 inputs rate (mk_usize 0) n l;
  let ks_abs = impl_absorb_loop_generic v_N ks0 inputs rate (mk_usize 0) n in
  lemma_absorb_final_generic v_N lc sc ks_abs inputs rate delim start remaining l
#pop-options
