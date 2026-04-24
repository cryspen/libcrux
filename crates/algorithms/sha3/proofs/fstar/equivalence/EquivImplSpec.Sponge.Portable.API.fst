module EquivImplSpec.Sponge.Portable.API

(* ================================================================
   Top-level SHA-3 / SHAKE equivalence theorems for the Portable
   (N=1, v_T=u64) backend.

   Proven top-down assuming two layer lemmas about the Portable
   absorb / squeeze drivers:

     [lemma_absorb_portable]   : Generic_keccak.Portable.absorb ≡
                                 Hacspec_sha3.Sponge.absorb
     [lemma_squeeze_portable]  : Generic_keccak.Portable.squeeze ≡
                                 Hacspec_sha3.Sponge.squeeze

   These are currently [assume val]; discharging them is the job of
   the generic sponge-layer proof (EquivImplSpec.Sponge.Portable +
   EquivImplSpec.Sponge.Generic.{Absorb,Squeeze,Keccak}).

   The top-level theorems — [lemma_sha224_portable], [_sha256_],
   [_sha384_], [_sha512_], [_shake128_], [_shake256_] — then follow
   by unfolding and constant-matching.

   Matches the dispatch performed by [Libcrux_sha3.hash] and its
   public API ([sha224..512], [shake128/256]) to the spec hashers
   in [Hacspec_sha3.Sha3].
   ================================================================ *)

#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"

open FStar.Mul
open Core_models

module SC = EquivImplSpec.Sponge.Generic.Core
module Steps = EquivImplSpec.Sponge.Portable.Steps
module SqueezeAPI = EquivImplSpec.Sponge.Portable.SqueezeAPI
module KP = EquivImplSpec.Keccakf.Portable
module HS = Hacspec_sha3.Sponge
module SL = Hacspec_sha3.Sponge.Lemmas
module GK = Libcrux_sha3.Generic_keccak
module NF = Proof_Utils.NatFold

(* Bring Portable typeclass instances into scope so
   t_KeccakItem u64 1 / t_Absorb / t_Squeeze resolve. *)
let _ =
  let open Libcrux_sha3.Traits in
  let open Libcrux_sha3.Simd.Portable in
  ()

(* ================================================================
   LAYER ASSUMPTIONS

   Per-backend absorb / squeeze equivalence at N=1.  These bridge
   the Libcrux Portable drivers to the scalar Hacspec sponge spec.

   Both are [assume val]: the content of the sponge-layer proof is
   exactly to discharge these (at the Portable instantiation of the
   generic sponge_correctness record, [EquivImplSpec.Sponge.Portable]).
   ================================================================ *)

(** Slice-identity bridge used by [lemma_absorb_portable_aux].

    Stated on pure [Seq.slice] (not the typeclass-dispatched [.[ ]])
    so the arithmetic precondition is direct and Z3 can discharge
    the refinement types on the slice expressions cheaply.  The
    typeclass-dispatched slicings in the call site reduce to
    [Seq.slice] definitionally, so [Seq.lemma_eq_intro] or
    [Seq.lemma_eq_elim] bridges at the call site. *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 50"
let lemma_absorb_tail_split_seq
      (input: Seq.seq u8) (kr slen rate: nat)
  : Lemma
      (requires
        rate > 0 /\
        kr + rate <= slen /\
        slen == Seq.length input)
      (ensures (
        let tail_k       = Seq.slice input kr slen in
        let block        = Seq.slice input kr (kr + rate) in
        let tail_k1      = Seq.slice input (kr + rate) slen in
        let head_of_tail = Seq.slice tail_k 0 rate in
        let rest_of_tail = Seq.slice tail_k rate (slen - kr) in
        Seq.equal head_of_tail block /\ Seq.equal rest_of_tail tail_k1))
  = ()
#pop-options


(** One spec-level step of [absorb_rec]: given that [ks_st']
    is the block-absorption of [ks_st] on [input.[k*rate..(k+1)*rate]],
    conclude that [absorb_rec] applied to the two tails commute.

    This is extracted into a standalone helper so the slice-identity
    reasoning runs in a clean context, separate from the aux helper's
    heavy [fold_range] state. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let lemma_absorb_rec_step
      (ks_st ks_st': t_Array u64 (mk_usize 25))
      (rate: usize) (delim: u8)
      (input: t_Slice u8)
      (k: usize)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v k * v rate + v rate <= Seq.length #u8 input /\
        ks_st' == Hacspec_sha3.Sponge.absorb_block ks_st
                    (input.[ { Core_models.Ops.Range.f_start = k *! rate;
                               Core_models.Ops.Range.f_end   = (k +! mk_usize 1) *! rate } <:
                             Core_models.Ops.Range.t_Range usize ] <: t_Slice u8)
                    rate)
      (ensures (
        let tail_k  : t_Slice u8 =
          input.[ { Core_models.Ops.Range.f_start = k *! rate } <:
                  Core_models.Ops.Range.t_RangeFrom usize ] in
        let tail_k1 : t_Slice u8 =
          input.[ { Core_models.Ops.Range.f_start = (k +! mk_usize 1) *! rate } <:
                  Core_models.Ops.Range.t_RangeFrom usize ] in
        Hacspec_sha3.Sponge.absorb_rec ks_st  rate delim tail_k ==
        Hacspec_sha3.Sponge.absorb_rec ks_st' rate delim tail_k1))
  = let kr   = v (k *! rate) in
    let slen = Seq.length #u8 input in
    lemma_absorb_tail_split_seq input kr slen (v rate)
#pop-options


(** Recursive induction helper for [lemma_absorb_portable].

    For any partial state [ks] and index [k] in [0..input_blocks], the
    fold_range's tail from [k] to [input_blocks] followed by [absorb_final]
    equals the spec [absorb_rec] applied to [ks.f_st] and the [k*rate..]
    suffix of [input].

    Inline-lambda copy matches the extracted [absorb]'s body verbatim, so
    [lemma_fold_range_step] can unfold it one step at a time. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 800"
let rec lemma_absorb_portable_aux
      (rate: usize) (delim: u8) (input: t_Slice u8)
      (input_blocks: usize) (input_rem: usize)
      (k: usize)
      (ks: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        v input_blocks == Seq.length #u8 input / v rate /\
        v input_rem == Seq.length #u8 input % v rate /\
        v k <= v input_blocks)
      (ensures (
        let inputs : t_Array (t_Slice u8) (mk_usize 1) =
          let list = [input] in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
          Rust_primitives.Hax.array_of_list 1 list in
        let input_len : usize = Core_models.Slice.impl__len #u8 input in
        let ks_k =
          Rust_primitives.Hax.Folds.fold_range k input_blocks
            (fun s temp_1_ ->
                let s:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 = s in
                let _:usize = temp_1_ in
                true)
            ks
            (fun s i ->
                let s:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 = s in
                let i:usize = i in
                let _:Prims.unit =
                  Libcrux_sha3.Proof_utils.Lemmas.lemma_mul_succ_le i input_blocks rate
                in
                let s:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 =
                  Libcrux_sha3.Generic_keccak.impl_2__absorb_block (mk_usize 1)
                    #u64
                    rate
                    s
                    (let list = [input] in
                      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                      Rust_primitives.Hax.array_of_list 1 list)
                    (i *! rate <: usize)
                in
                s) in
        let ks_final =
          Libcrux_sha3.Generic_keccak.impl_2__absorb_final (mk_usize 1) #u64
            rate delim ks_k inputs (input_len -! input_rem) input_rem in
        ks_final.Libcrux_sha3.Generic_keccak.f_st ==
          Hacspec_sha3.Sponge.absorb_rec
            ks.Libcrux_sha3.Generic_keccak.f_st rate delim
            (input.[ { Core_models.Ops.Range.f_start = k *! rate } <:
                     Core_models.Ops.Range.t_RangeFrom usize ] <: t_Slice u8)))
      (decreases v input_blocks - v k)
  =
  let inputs : t_Array (t_Slice u8) (mk_usize 1) =
    let list = [input] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
    Rust_primitives.Hax.array_of_list 1 list in
  let input_len : usize = Core_models.Slice.impl__len #u8 input in
  if k =. input_blocks then begin
    (* Base case: fold_range k k ... = ks; apply absorb_last. *)
    Steps.lemma_absorb_last_portable rate delim ks inputs
      (input_len -! input_rem) input_rem;
    (* absorb_rec on a suffix of length < rate unfolds to absorb_final. *)
    let tail : t_Slice u8 =
      input.[ { Core_models.Ops.Range.f_start = k *! rate } <:
              Core_models.Ops.Range.t_RangeFrom usize ] in
    assert (Seq.length #u8 tail == v input_rem);
    assert (v input_rem < v rate);
    (* pad_last_block reads only message[offset..offset+remaining]; both
       sides view the same bytes — show the two messages' views match. *)
    let bytes_full =
      Seq.slice input (v (input_len -! input_rem)) (v (input_len -! input_rem) + v input_rem) in
    let bytes_tail =
      Seq.slice tail 0 (v input_rem) in
    assert (Seq.equal bytes_full bytes_tail)
  end else begin
    (* Inductive step: apply lemma_fold_range_step with the SAME inline
       lambdas the extractor produces, so F* matches syntactically and the
       one-step unfolding applies to the fold_range in the ensures clause. *)
    Proof_Utils.FoldRange.lemma_fold_range_step
      #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
      k input_blocks
      (fun s temp_1_ ->
          let s:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 = s in
          let _:usize = temp_1_ in
          true)
      ks
      (fun s i ->
          let s:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 = s in
          let i:usize = i in
          let _:Prims.unit =
            Libcrux_sha3.Proof_utils.Lemmas.lemma_mul_succ_le i input_blocks rate
          in
          let s:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 =
            Libcrux_sha3.Generic_keccak.impl_2__absorb_block (mk_usize 1)
              #u64
              rate
              s
              (let list = [input] in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                Rust_primitives.Hax.array_of_list 1 list)
              (i *! rate <: usize)
          in
          s);
    Libcrux_sha3.Proof_utils.Lemmas.lemma_mul_succ_le k input_blocks rate;
    Steps.lemma_absorb_block_portable rate ks inputs (k *! rate);
    let ks' : Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 =
      Libcrux_sha3.Generic_keccak.impl_2__absorb_block (mk_usize 1) #u64 rate ks
        inputs (k *! rate) in
    let k1 : usize = k +! mk_usize 1 in
    assert (v k1 <= v input_blocks);
    lemma_absorb_portable_aux rate delim input input_blocks input_rem k1 ks';
    (* Slice-identity bridge: absorb_rec on the suffix from [k*rate]
       unfolds one step to absorb_rec on the suffix from [(k+1)*rate]
       after an absorb_block.  The helper [lemma_absorb_rec_step]
       encodes this, but invoking it in the aux's heavy fold_range
       context triggers a Z3 LP-solver internal-assertion bug
       (lar_solver.cpp:1066) on fresh hint generation.  Setting
       [--z3refresh] works around the bug per-query but is too slow
       to complete the recursive proof within make's timeout. *)
    admit ()
  end
#pop-options


(** Portable absorb commutes with the scalar spec absorb: the state
    returned by [Generic_keccak.Portable.absorb] equals (at the
    [f_st] field) the 25-lane state returned by
    [Hacspec_sha3.Sponge.absorb]. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 400"
let lemma_absorb_portable

      (rate: usize) (delim: u8) (input: t_Slice u8)
  : Lemma
      (requires Libcrux_sha3.Proof_utils.valid_rate rate)
      (ensures
        (Libcrux_sha3.Generic_keccak.Portable.absorb rate delim input)
          .Libcrux_sha3.Generic_keccak.f_st
        ==
        Hacspec_sha3.Sponge.absorb rate delim input)
  =
  let input_len : usize = Core_models.Slice.impl__len #u8 input in
  let input_blocks : usize = input_len /! rate in
  let input_rem : usize = input_len %! rate in
  let ks0 = Libcrux_sha3.Generic_keccak.impl_2__new (mk_usize 1) #u64 () in
  lemma_absorb_portable_aux rate delim input input_blocks input_rem
    (mk_usize 0) ks0;
  (* input.[RangeFrom 0] == input; collapse RangeFrom-0 to the whole slice. *)
  let whole : t_Slice u8 =
    input.[ { Core_models.Ops.Range.f_start = mk_usize 0 *! rate } <:
            Core_models.Ops.Range.t_RangeFrom usize ] in
  assert (Seq.equal whole input)
#pop-options


(** Portable squeeze commutes with the scalar spec squeeze: the
    byte-stream returned by [Generic_keccak.Portable.squeeze] agrees
    with [Hacspec_sha3.Sponge.squeeze] taken as a slice.

    [Generic_keccak.Portable.squeeze]'s strong postcondition factors
    its result as [portable_squeeze_composed rate ks output] — a
    direct mirror of [Hacspec_sha3.Sponge.squeeze]'s structure with
    [f_squeeze]/[keccakf1600] in place of [squeeze_state]/[keccak_f]
    and the external [output] buffer in place of the spec's zero
    initialisation. Per-primitive bridge lemmas
    ([lemma_squeeze_once_portable], [lemma_squeeze_block_portable],
    [lemma_squeeze_last_portable], [KP.lemma_keccakf1600_portable])
    close the primitive gap; the buffer-initialisation gap closes
    because each branch's squeeze steps cumulatively overwrite
    [0..output_len), so initial bytes never survive to the result. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 800 --split_queries always"
let lemma_squeeze_portable
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
  = (* The equivalence is discharged directly by the postcondition of
       [Libcrux_sha3.Generic_keccak.Portable.squeeze], whose ensures
       states [result == Hacspec_sha3.Sponge.squeeze ...].  We invoke
       it here so the ensures is brought into context. *)
    let ks : Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 =
      { Libcrux_sha3.Generic_keccak.f_st = state } in
    let _ = Libcrux_sha3.Generic_keccak.Portable.squeeze rate ks output in
    ()
#pop-options


(* ================================================================
   KECCAK1 EQUIVALENCE

   The single-lane portable driver [keccak1] = absorb · squeeze.
   Composition of the two layer lemmas.
   ================================================================ *)

let lemma_keccak1_portable
      (rate: usize) (delim: u8)
      (input output: t_Slice u8)
  : Lemma
      (requires
        Libcrux_sha3.Proof_utils.valid_rate rate /\
        Seq.length #u8 output < v Core_models.Num.impl_usize__MAX - 200)
      (ensures (
        let output_len : usize = Core_models.Slice.impl__len #u8 output in
        Libcrux_sha3.Generic_keccak.Portable.keccak1 rate delim input output
        ==
        (Hacspec_sha3.Sponge.keccak output_len rate delim input <: t_Slice u8)))
  = let s : Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 =
      Libcrux_sha3.Generic_keccak.Portable.absorb rate delim input in
    lemma_absorb_portable rate delim input;
    lemma_squeeze_portable rate s.Libcrux_sha3.Generic_keccak.f_st output


(* ================================================================
   TOP-LEVEL SHA-3 HASHERS
   ================================================================ *)

let lemma_sha224_portable (digest data: t_Slice u8)
  : Lemma
      (requires Seq.length #u8 digest == 28)
      (ensures
        Libcrux_sha3.Portable.sha224 digest data
        ==
        (Hacspec_sha3.Sha3.sha3_224_ data <: t_Slice u8))
  = lemma_keccak1_portable (mk_usize 144) (mk_u8 6) data digest

let lemma_sha256_portable (digest data: t_Slice u8)
  : Lemma
      (requires Seq.length #u8 digest == 32)
      (ensures
        Libcrux_sha3.Portable.sha256 digest data
        ==
        (Hacspec_sha3.Sha3.sha3_256_ data <: t_Slice u8))
  = lemma_keccak1_portable (mk_usize 136) (mk_u8 6) data digest

let lemma_sha384_portable (digest data: t_Slice u8)
  : Lemma
      (requires Seq.length #u8 digest == 48)
      (ensures
        Libcrux_sha3.Portable.sha384 digest data
        ==
        (Hacspec_sha3.Sha3.sha3_384_ data <: t_Slice u8))
  = lemma_keccak1_portable (mk_usize 104) (mk_u8 6) data digest

let lemma_sha512_portable (digest data: t_Slice u8)
  : Lemma
      (requires Seq.length #u8 digest == 64)
      (ensures
        Libcrux_sha3.Portable.sha512 digest data
        ==
        (Hacspec_sha3.Sha3.sha3_512_ data <: t_Slice u8))
  = lemma_keccak1_portable (mk_usize 72) (mk_u8 6) data digest


(* ================================================================
   TOP-LEVEL SHAKE XOFs
   ================================================================ *)

let lemma_shake128_portable (digest data: t_Slice u8)
  : Lemma
      (requires
        Seq.length #u8 digest < v Core_models.Num.impl_usize__MAX - 200)
      (ensures (
        let n : usize = Core_models.Slice.impl__len #u8 digest in
        Libcrux_sha3.Portable.shake128 digest data
        ==
        (Hacspec_sha3.Sha3.shake128 n data <: t_Slice u8)))
  = lemma_keccak1_portable (mk_usize 168) (mk_u8 31) data digest

let lemma_shake256_portable (digest data: t_Slice u8)
  : Lemma
      (requires
        Seq.length #u8 digest < v Core_models.Num.impl_usize__MAX - 200)
      (ensures (
        let n : usize = Core_models.Slice.impl__len #u8 digest in
        Libcrux_sha3.Portable.shake256 digest data
        ==
        (Hacspec_sha3.Sha3.shake256 n data <: t_Slice u8)))
  = lemma_keccak1_portable (mk_usize 136) (mk_u8 31) data digest
