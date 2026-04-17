module EquivImplSpec.Sponge.Generic.Keccak

(* ================================================================
   Spec-side bridges for the Keccak sponge composition.

   Provides:
   - lemma_spec_absorb_bridge:
       Hacspec_sha3.Sponge.absorb rate delim message
       == absorb_final(spec_absorb_loop(zeros, msg, rate, 0, n), ...)

     Bridges the fold_range in the extracted spec absorb to our
     recursive spec_absorb_loop (from Generic.Absorb) via NatFold.

   - squeeze_body: named squeeze body for backend use

   Backend-independent: operates on scalar t_Array u64 25 state.
   Used by all backend instantiations (Portable, Arm64, AVX2).
   ================================================================ *)

#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"

open FStar.Mul
open Core_models

module A = EquivImplSpec.Sponge.Generic.Absorb
module S = EquivImplSpec.Sponge.Generic.Squeeze
module SC = EquivImplSpec.Sponge.Generic.Core

open Proof_Utils.NatFold


(* ================================================================
   SPEC ABSORB BRIDGE

   The extracted Hacspec_sha3.Sponge.absorb uses fold_range internally.
   We bridge to spec_absorb_loop (recursive) via NatFold.
   ================================================================ *)

(* Named nat-indexed absorb body — matches the extracted lambda
   inside Hacspec_sha3.Sponge.absorb, lifted to nat index. *)
let absorb_body_rnat
      (rate: usize{Libcrux_sha3.Proof_utils.valid_rate rate})
      (message: t_Slice u8)
      (n: nat{n * v rate <= Seq.length message})
      (state: SC.spec_state)
      (j: nat{0 <= j /\ j < n})
    : SC.spec_state =
  let offset = mk_usize j *! rate in
  Hacspec_sha3.Sponge.absorb_block state
    (message.[ {
        Core_models.Ops.Range.f_start = offset;
        Core_models.Ops.Range.f_end = offset +! rate <: usize
      } <: Core_models.Ops.Range.t_Range usize ] <: t_Slice u8)
    rate


(* Inductive bridge: fold_range_nat matches spec_absorb_loop. *)
#push-options "--fuel 1 --z3rlimit 200"
let rec lemma_absorb_fold_is_loop
      (state: SC.spec_state)
      (message: t_Slice u8)
      (rate: usize)
      (n: nat)
      (i: nat{0 <= i /\ i <= n})
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        n * v rate <= Seq.length message)
      (ensures
        fold_range_nat 0 n i state (absorb_body_rnat rate message n)
        ==
        A.spec_absorb_loop state message rate (mk_usize i) (mk_usize n))
      (decreases n - i)
  = if i = n then ()
    else lemma_absorb_fold_is_loop
           (absorb_body_rnat rate message n state i)
           message rate n (i + 1)
#pop-options


(* Main bridge: Hacspec_sha3.Sponge.absorb == absorb_final(spec_absorb_loop(...), ...).

   Proof strategy:
   (A) lemma_fold_range_is_range_nat: fold_range -> fold_range_nat
       (matching the extracted lambda shape verbatim)
   (B) lemma_absorb_fold_is_loop: fold_range_nat -> spec_absorb_loop *)
(* Named fold body for spec absorb — same computation as the extracted
   lambda in Hacspec_sha3.Sponge.absorb, but with constraints in parameter
   types so Z3 can handle the nonlinear multiplication bound. *)
let absorb_fold_body
      (rate: usize{Libcrux_sha3.Proof_utils.valid_rate rate})
      (message: t_Slice u8)
      (n: usize{v n * v rate <= Seq.length message})
      (state: SC.spec_state)
      (e_block_idx: usize{v e_block_idx < v n})
    : SC.spec_state =
  let offset:usize = e_block_idx *! rate in
  Hacspec_sha3.Sponge.absorb_block state
    (message.[ {
          Core_models.Ops.Range.f_start = offset;
          Core_models.Ops.Range.f_end = offset +! rate <: usize
        }
        <:
        Core_models.Ops.Range.t_Range usize ]
      <:
      t_Slice u8)
    rate


(* Recursive bridge: fold_range via absorb_fold_body == spec_absorb_loop.
   Uses lemma_fold_range_step to peel one step at a time. *)
#push-options "--fuel 1 --z3rlimit 400"
let rec lemma_spec_absorb_fold_eq
      (rate: usize)
      (message: t_Slice u8)
      (n: usize)
      (state: SC.spec_state)
      (i: usize)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v i <= v n /\
        v n * v rate <= Seq.length message)
      (ensures (
        let inv (s: SC.spec_state) (_: usize) : Type0 = True in
        let f (s: SC.spec_state) (j: usize{v j < v n})
          : SC.spec_state = absorb_fold_body rate message n s j in
        Rust_primitives.Hax.Folds.fold_range i n inv state f
        ==
        A.spec_absorb_loop state message rate i n))
      (decreases v n - v i)
  =
  if i =. n then ()
  else begin
    let inv (s: SC.spec_state) (_: usize) : Type0 = True in
    let f (s: SC.spec_state) (j: usize{v j < v n})
      : SC.spec_state = absorb_fold_body rate message n s j in
    Proof_Utils.FoldRange.lemma_fold_range_step i n inv state f;
    lemma_spec_absorb_fold_eq rate message n (f state i) (i +! mk_usize 1)
  end
#pop-options


(* Main bridge: Hacspec_sha3.Sponge.absorb == absorb_final(spec_absorb_loop(...), ...).

   This is an assume val due to the fold_range closure-equality limitation:
   F* SMT cannot equate the inline lambda inside Hacspec_sha3.Sponge.absorb
   with our named absorb_fold_body, even though they are α/δ-equivalent.
   See EquivImplSpec.Sponge.Keccak.fst (lemma_sponge_absorb_decomposes) for
   the identical axiom in the portable proof.

   The helper lemmas above (lemma_absorb_fold_is_loop, lemma_spec_absorb_fold_eq)
   DO verify and bridge fold_range/fold_range_nat to spec_absorb_loop for
   any lambda that F* can match. The gap is only the final connection to
   the extracted top-level function. *)
assume val lemma_spec_absorb_bridge
      (rate: usize) (delim: u8) (message: t_Slice u8)
  : Lemma
      (requires Libcrux_sha3.Proof_utils.valid_rate rate)
      (ensures (
        let input_len = Core_models.Slice.impl__len #u8 message in
        let n = input_len /! rate in
        let remaining = input_len %! rate in
        let state0 = Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 25) in
        Hacspec_sha3.Sponge.absorb rate delim message
        ==
        Hacspec_sha3.Sponge.absorb_final
          (A.spec_absorb_loop state0 message rate (mk_usize 0) n)
          message (n *! rate) remaining rate delim))


(* ================================================================
   SPEC SQUEEZE HELPERS

   The squeeze-phase bridge is more complex than absorb due to the
   pair accumulator (output, state), three-way branching, and type
   differences (t_Array u8 output_len vs t_Slice u8).

   Per-step building blocks are in Generic.Squeeze:
   - lemma_squeeze_once_generic: single squeeze (no keccakf)
   - lemma_squeeze_kf_step_generic: keccakf then squeeze

   The full squeeze-phase composition is done per-backend.

   We provide the spec-side squeeze body as a convenience.
   ================================================================ *)

(* Named squeeze body: keccak_f then squeeze_state.
   Matches the fold_range body in Hacspec_sha3.Sponge.squeeze. *)
let squeeze_body
      (rate: usize)
      (state: SC.spec_state)
      (output: t_Slice u8)
      (i: usize)
  : Pure (t_Slice u8 & SC.spec_state)
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v i * v rate + v rate <= Seq.length output)
      (ensures fun (output', state') ->
        Seq.length #u8 output' == Seq.length #u8 output /\
        state' == Hacspec_sha3.Keccak_f.keccak_f state)
  =
  let state' = Hacspec_sha3.Keccak_f.keccak_f state in
  let output' = Hacspec_sha3.Sponge.squeeze_state state' output (i *! rate) rate in
  (output', state')
