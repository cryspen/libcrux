module Libcrux_sha3.Generic_keccak.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_sha3.Simd.Portable in
  let open Libcrux_sha3.Traits in
  ()

#push-options "--z3rlimit 800"

let e_keccak_state_impl_opts (_: Prims.unit) : Prims.unit = ()

let impl__squeeze_next_block
      (v_RATE: usize)
      (self: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
      (out: t_Slice u8)
      (start: usize)
    : Prims.Pure (Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 & t_Slice u8)
      (requires
        Libcrux_sha3.Proof_utils.valid_rate v_RATE &&
        ((Rust_primitives.Hax.Int.from_machine start <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine v_RATE <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine (Core_models.Slice.impl__len #u8 out <: usize)
          <:
          Hax_lib.Int.t_Int))
      (ensures
        fun temp_0_ ->
          let
          (self_e_future: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64),
          (out_future: t_Slice u8) =
            temp_0_
          in
          (Core_models.Slice.impl__len #u8 out_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out <: usize)) =
  let self:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 =
    Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 (mk_usize 1) #u64 self
  in
  let out:t_Slice u8 =
    Libcrux_sha3.Traits.f_squeeze #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
      #u64
      #FStar.Tactics.Typeclasses.solve
      v_RATE
      self
      out
      start
      v_RATE
  in
  self, out <: (Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 & t_Slice u8)

let impl__squeeze_first_block
      (v_RATE: usize)
      (self: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
      (out: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        Libcrux_sha3.Proof_utils.valid_rate v_RATE &&
        v_RATE <=. (Core_models.Slice.impl__len #u8 out <: usize))
      (ensures
        fun out_future ->
          let out_future:t_Slice u8 = out_future in
          (Core_models.Slice.impl__len #u8 out_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out <: usize)) =
  let out:t_Slice u8 =
    Libcrux_sha3.Traits.f_squeeze #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
      #u64
      #FStar.Tactics.Typeclasses.solve
      v_RATE
      self
      out
      (mk_usize 0)
      v_RATE
  in
  out

let impl__squeeze_first_three_blocks
      (v_RATE: usize)
      (self: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
      (out: t_Slice u8)
    : Prims.Pure (Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 & t_Slice u8)
      (requires
        Libcrux_sha3.Proof_utils.valid_rate v_RATE &&
        (mk_usize 3 *! v_RATE <: usize) <=. (Core_models.Slice.impl__len #u8 out <: usize))
      (ensures
        fun temp_0_ ->
          let
          (self_e_future: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64),
          (out_future: t_Slice u8) =
            temp_0_
          in
          (Core_models.Slice.impl__len #u8 out_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out <: usize)) =
  let out:t_Slice u8 =
    Libcrux_sha3.Traits.f_squeeze #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
      #u64
      #FStar.Tactics.Typeclasses.solve
      v_RATE
      self
      out
      (mk_usize 0)
      v_RATE
  in
  let self:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 =
    Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 (mk_usize 1) #u64 self
  in
  let out:t_Slice u8 =
    Libcrux_sha3.Traits.f_squeeze #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
      #u64
      #FStar.Tactics.Typeclasses.solve
      v_RATE
      self
      out
      v_RATE
      v_RATE
  in
  let self:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 =
    Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 (mk_usize 1) #u64 self
  in
  let out:t_Slice u8 =
    Libcrux_sha3.Traits.f_squeeze #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
      #u64
      #FStar.Tactics.Typeclasses.solve
      v_RATE
      self
      out
      (mk_usize 2 *! v_RATE <: usize)
      v_RATE
  in
  self, out <: (Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 & t_Slice u8)

let impl__squeeze_first_five_blocks
      (v_RATE: usize)
      (self: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
      (out: t_Slice u8)
    : Prims.Pure (Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 & t_Slice u8)
      (requires
        Libcrux_sha3.Proof_utils.valid_rate v_RATE &&
        (mk_usize 5 *! v_RATE <: usize) <=. (Core_models.Slice.impl__len #u8 out <: usize))
      (ensures
        fun temp_0_ ->
          let
          (self_e_future: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64),
          (out_future: t_Slice u8) =
            temp_0_
          in
          (Core_models.Slice.impl__len #u8 out_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out <: usize)) =
  let out:t_Slice u8 =
    Libcrux_sha3.Traits.f_squeeze #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
      #u64
      #FStar.Tactics.Typeclasses.solve
      v_RATE
      self
      out
      (mk_usize 0)
      v_RATE
  in
  let self:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 =
    Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 (mk_usize 1) #u64 self
  in
  let out:t_Slice u8 =
    Libcrux_sha3.Traits.f_squeeze #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
      #u64
      #FStar.Tactics.Typeclasses.solve
      v_RATE
      self
      out
      v_RATE
      v_RATE
  in
  let self:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 =
    Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 (mk_usize 1) #u64 self
  in
  let out:t_Slice u8 =
    Libcrux_sha3.Traits.f_squeeze #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
      #u64
      #FStar.Tactics.Typeclasses.solve
      v_RATE
      self
      out
      (mk_usize 2 *! v_RATE <: usize)
      v_RATE
  in
  let self:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 =
    Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 (mk_usize 1) #u64 self
  in
  let out:t_Slice u8 =
    Libcrux_sha3.Traits.f_squeeze #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
      #u64
      #FStar.Tactics.Typeclasses.solve
      v_RATE
      self
      out
      (mk_usize 3 *! v_RATE <: usize)
      v_RATE
  in
  let self:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 =
    Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 (mk_usize 1) #u64 self
  in
  let out:t_Slice u8 =
    Libcrux_sha3.Traits.f_squeeze #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
      #u64
      #FStar.Tactics.Typeclasses.solve
      v_RATE
      self
      out
      (mk_usize 4 *! v_RATE <: usize)
      v_RATE
  in
  self, out <: (Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 & t_Slice u8)

#push-options "--z3rlimit 300"

/// Absorb phase of `keccak1`: initialise a Keccak state, absorb all full
/// rate-byte blocks of `input`, then pad and absorb the final partial block
/// with domain-separation byte `DELIM` and the pad10*1 terminator.
let absorb (v_RATE: usize) (v_DELIM: u8) (input: t_Slice u8)
    : Prims.Pure (Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
      (requires Libcrux_sha3.Proof_utils.valid_rate v_RATE)
      (fun _ -> Prims.l_True) =
  let s:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 =
    Libcrux_sha3.Generic_keccak.impl_2__new (mk_usize 1) #u64 ()
  in
  let input_len:usize = Core_models.Slice.impl__len #u8 input in
  let input_blocks:usize = input_len /! v_RATE in
  let input_rem:usize = input_len %! v_RATE in
  let s:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      input_blocks
      (fun s temp_1_ ->
          let s:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 = s in
          let _:usize = temp_1_ in
          true)
      s
      (fun s i ->
          let s:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 = s in
          let i:usize = i in
          let _:Prims.unit =
            Libcrux_sha3.Proof_utils.Lemmas.lemma_mul_succ_le i input_blocks v_RATE
          in
          let s:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 =
            Libcrux_sha3.Generic_keccak.impl_2__absorb_block (mk_usize 1)
              #u64
              v_RATE
              s
              (let list = [input] in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                Rust_primitives.Hax.array_of_list 1 list)
              (i *! v_RATE <: usize)
          in
          s)
  in
  let s:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 =
    Libcrux_sha3.Generic_keccak.impl_2__absorb_final (mk_usize 1)
      #u64
      v_RATE
      v_DELIM
      s
      (let list = [input] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
        Rust_primitives.Hax.array_of_list 1 list)
      (input_len -! input_rem <: usize)
      input_rem
  in
  s

#pop-options

#push-options "--fuel 0 --ifuel 1 --z3rlimit 800 --split_queries always"

/// Squeeze phase of `keccak1`: extract `output.len()` bytes from `s`,
/// applying Keccak-f between each full rate-byte block of output.
/// The ensures clause factors the result as a composition of impl
/// primitives (`f_squeeze`, `keccakf1600`) and the spec\'s recursive
/// `squeeze_blocks`:
///   * `output_blocks == 0`: a single `f_squeeze` of `output_len` bytes.
///   * `output_blocks > 0`:
///       let `output1 = f_squeeze RATE s output 0 RATE`
///       let `(st_mid, out_mid) = squeeze_blocks output_len s.st RATE 1 output_blocks output1`
///       if `output_rem == 0`: `out_mid`
///       else: `f_squeeze RATE (keccakf1600 {st = st_mid}) out_mid (output_len - output_rem) output_rem`
/// This is a *direct* consequence of the loop\'s semantics and does not
/// require buffer-locality reasoning: the first and last blocks are
/// stated in impl primitives, and the middle loop\'s invariant tracks
/// (state, output) through `squeeze_blocks` anchored at `output1`.
/// Preservation is discharged by the spec-side `lemma_squeeze_blocks_tail`
/// (right-extends the recursion) together with the per-block impl-to-spec
/// bridge `lemma_squeeze_block_portable`. An external lemma
/// (`EquivImplSpec.Sponge.Portable.API.lemma_squeeze_portable`) then
/// reconciles this composition with `Hacspec_sha3.Sponge.squeeze`.
let squeeze
      (v_RATE: usize)
      (s: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
      (output: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        Libcrux_sha3.Proof_utils.valid_rate v_RATE &&
        (Core_models.Slice.impl__len #u8 output <: usize) <.
        (Core_models.Num.impl_usize__MAX -! mk_usize 200 <: usize))
      (ensures
        fun output_future ->
          let output_future:t_Slice u8 = output_future in
          b2t
          ((Core_models.Slice.impl__len #u8 output_future <: usize) =.
            (Core_models.Slice.impl__len #u8 output <: usize)
            <:
            bool) /\
          (output_future <: t_Slice u8) ==
          (EquivImplSpec.Sponge.Portable.Steps.portable_squeeze_composed v_RATE s output
            <:
            t_Slice u8)) =
  let output_len:usize = Core_models.Slice.impl__len #u8 output in
  let output_blocks:usize = output_len /! v_RATE in
  let output_rem:usize = output_len %! v_RATE in
  let s_init_st:t_Array u64 (mk_usize 25) = s.Libcrux_sha3.Generic_keccak.f_st in
  let (output: t_Slice u8), (s: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64) =
    if output_blocks =. mk_usize 0
    then
      let output:t_Slice u8 =
        Libcrux_sha3.Traits.f_squeeze #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
          #u64
          #FStar.Tactics.Typeclasses.solve
          v_RATE
          s
          output
          (mk_usize 0)
          output_len
      in
      output, s <: (t_Slice u8 & Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
    else
      let output:t_Slice u8 =
        Libcrux_sha3.Traits.f_squeeze #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
          #u64
          #FStar.Tactics.Typeclasses.solve
          v_RATE
          s
          output
          (mk_usize 0)
          v_RATE
      in
      let out1:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = Alloc.Slice.impl__to_vec #u8 output in
      let _:Prims.unit =
        let out1_arr:t_Array u8 output_len = Alloc.Vec.impl_1__as_slice out1 <: t_Slice _ in
        Libcrux_sha3.Proof_utils.Lemmas.lemma_div_mul_mod output_len v_RATE;
        Hacspec_sha3.Sponge.Lemmas.lemma_squeeze_blocks_base output_len
          s_init_st
          v_RATE
          (mk_usize 1)
          out1_arr
      in
      let (output: t_Slice u8), (s: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64) =
        Rust_primitives.Hax.Folds.fold_range (mk_usize 1)
          output_blocks
          (fun temp_0_ i ->
              let
              (output: t_Slice u8), (s: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
              =
                temp_0_
              in
              let i:usize = i in
              b2t ((Core_models.Slice.impl__len #u8 output <: usize) =. output_len <: bool) /\
              (let out1_arr:t_Array u8 output_len = Alloc.Vec.impl_1__as_slice out1 <: t_Slice _ in
                let st, out =
                  Hacspec_sha3.Sponge.squeeze_blocks output_len
                    s_init_st
                    v_RATE
                    (mk_usize 1)
                    i
                    out1_arr
                in
                s.Libcrux_sha3.Generic_keccak.f_st == st /\
                (output <: t_Slice u8) == (out <: t_Slice u8)))
          (output, s <: (t_Slice u8 & Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64))
          (fun temp_0_ i ->
              let
              (output: t_Slice u8), (s: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
              =
                temp_0_
              in
              let i:usize = i in
              let _:Prims.unit =
                Libcrux_sha3.Proof_utils.Lemmas.lemma_mul_succ_le i output_blocks v_RATE
              in
              let _:Prims.unit =
                let out1_arr:t_Array u8 output_len = Alloc.Vec.impl_1__as_slice out1 <: t_Slice _ in
                Libcrux_sha3.Proof_utils.Lemmas.lemma_div_mul_mod output_len v_RATE;
                Libcrux_sha3.Proof_utils.Lemmas.lemma_mul_succ_le i output_blocks v_RATE;
                assert (v i * v v_RATE + v v_RATE <= v output_len);
                let start:usize = i *! v_RATE in
                Hacspec_sha3.Sponge.Lemmas.lemma_squeeze_blocks_tail output_len
                  s_init_st
                  v_RATE
                  (mk_usize 1)
                  i
                  (i +! mk_usize 1)
                  out1_arr;
                EquivImplSpec.Sponge.Portable.Steps.lemma_squeeze_block_portable v_RATE
                  s
                  output
                  start
              in
              let s:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 =
                Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 (mk_usize 1) #u64 s
              in
              let output:t_Slice u8 =
                Libcrux_sha3.Traits.f_squeeze #(Libcrux_sha3.Generic_keccak.t_KeccakState
                      (mk_usize 1) u64)
                  #u64
                  #FStar.Tactics.Typeclasses.solve
                  v_RATE
                  s
                  output
                  (i *! v_RATE <: usize)
                  v_RATE
              in
              output, s <: (t_Slice u8 & Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
          )
      in
      if output_rem <>. mk_usize 0
      then
        let s:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 =
          Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 (mk_usize 1) #u64 s
        in
        let output:t_Slice u8 =
          Libcrux_sha3.Traits.f_squeeze #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64
            )
            #u64
            #FStar.Tactics.Typeclasses.solve
            v_RATE
            s
            output
            (output_len -! output_rem <: usize)
            output_rem
        in
        output, s <: (t_Slice u8 & Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
      else output, s <: (t_Slice u8 & Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
  in
  output

#pop-options

let keccak1 (v_RATE: usize) (v_DELIM: u8) (input output: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        Libcrux_sha3.Proof_utils.valid_rate v_RATE &&
        (Core_models.Slice.impl__len #u8 output <: usize) <.
        (Core_models.Num.impl_usize__MAX -! mk_usize 200 <: usize))
      (ensures
        fun output_future ->
          let output_future:t_Slice u8 = output_future in
          (Core_models.Slice.impl__len #u8 output_future <: usize) =.
          (Core_models.Slice.impl__len #u8 output <: usize)) =
  let s:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64 = absorb v_RATE v_DELIM input in
  let output:t_Slice u8 = squeeze v_RATE s output in
  output
