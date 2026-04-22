module Libcrux_sha3.Generic_keccak.Simd128
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_sha3.Simd.Arm64 in
  let open Libcrux_sha3.Traits in
  ()

#push-options "--z3rlimit 300"

/// Absorb phase of `keccak2`: initialise a two-lane Keccak state,
/// absorb all full rate-byte blocks of `data[0]` and `data[1]` in
/// parallel, then pad and absorb each lane\'s final partial block
/// with domain-separation byte `DELIM` and the pad10*1 terminator.
let absorb2 (v_RATE: usize) (v_DELIM: u8) (data: t_Array (t_Slice u8) (mk_usize 2))
    : Prims.Pure
      (Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
          Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t)
      (requires
        Libcrux_sha3.Proof_utils.valid_rate v_RATE &&
        (Core_models.Slice.impl__len #u8 (data.[ mk_usize 0 ] <: t_Slice u8) <: usize) =.
        (Core_models.Slice.impl__len #u8 (data.[ mk_usize 1 ] <: t_Slice u8) <: usize))
      (fun _ -> Prims.l_True) =
  let s:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
    Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t =
    Libcrux_sha3.Generic_keccak.impl_2__new (mk_usize 2)
      #Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t
      ()
  in
  let data_len:usize = Core_models.Slice.impl__len #u8 (data.[ mk_usize 0 ] <: t_Slice u8) in
  let data_blocks:usize = data_len /! v_RATE in
  let s:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
    Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      data_blocks
      (fun s temp_1_ ->
          let s:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
            Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t =
            s
          in
          let _:usize = temp_1_ in
          true)
      s
      (fun s i ->
          let s:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
            Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t =
            s
          in
          let i:usize = i in
          let _:Prims.unit =
            Libcrux_sha3.Proof_utils.Lemmas.lemma_mul_succ_le i data_blocks v_RATE
          in
          let s:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
            Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t =
            Libcrux_sha3.Generic_keccak.impl_2__absorb_block (mk_usize 2)
              #Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t
              v_RATE
              s
              data
              (i *! v_RATE <: usize)
          in
          s)
  in
  let rem:usize = data_len %! v_RATE in
  let s:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
    Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t =
    Libcrux_sha3.Generic_keccak.impl_2__absorb_final (mk_usize 2)
      #Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t
      v_RATE
      v_DELIM
      s
      data
      (data_len -! rem <: usize)
      rem
  in
  s

#pop-options

#push-options "--z3rlimit 300"

/// Squeeze phase of `keccak2`: extract `out0.len()` bytes from each
/// lane of `s` into `out0` and `out1`, applying Keccak-f between
/// each full rate-byte block of output.
let squeeze2
      (v_RATE: usize)
      (s:
          Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
            Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t)
      (out0 out1: t_Slice u8)
    : Prims.Pure (t_Slice u8 & t_Slice u8)
      (requires
        Libcrux_sha3.Proof_utils.valid_rate v_RATE &&
        (Core_models.Slice.impl__len #u8 out0 <: usize) =.
        (Core_models.Slice.impl__len #u8 out1 <: usize))
      (ensures
        fun temp_0_ ->
          let (out0_future: t_Slice u8), (out1_future: t_Slice u8) = temp_0_ in
          (Core_models.Slice.impl__len #u8 out0_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out0 <: usize) &&
          (Core_models.Slice.impl__len #u8 out1_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out1 <: usize)) =
  let out0_len:usize = Core_models.Slice.impl__len #u8 out0 in
  let out1_len:usize = Core_models.Slice.impl__len #u8 out1 in
  let outlen:usize = Core_models.Slice.impl__len #u8 out0 in
  let blocks:usize = outlen /! v_RATE in
  let last:usize = outlen -! (outlen %! v_RATE <: usize) in
  let
  (out0: t_Slice u8),
  (out1: t_Slice u8),
  (s:
    Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
      Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t) =
    if blocks =. mk_usize 0
    then
      let (tmp0: t_Slice u8), (tmp1: t_Slice u8) =
        Libcrux_sha3.Traits.f_squeeze2 #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
              Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t)
          #Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t
          #FStar.Tactics.Typeclasses.solve
          v_RATE
          s
          out0
          out1
          (mk_usize 0)
          outlen
      in
      let out0:t_Slice u8 = tmp0 in
      let out1:t_Slice u8 = tmp1 in
      let _:Prims.unit = () in
      out0, out1, s
      <:
      (t_Slice u8 & t_Slice u8 &
        Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
          Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t)
    else
      let (tmp0: t_Slice u8), (tmp1: t_Slice u8) =
        Libcrux_sha3.Traits.f_squeeze2 #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
              Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t)
          #Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t
          #FStar.Tactics.Typeclasses.solve
          v_RATE
          s
          out0
          out1
          (mk_usize 0)
          v_RATE
      in
      let out0:t_Slice u8 = tmp0 in
      let out1:t_Slice u8 = tmp1 in
      let _:Prims.unit = () in
      let
      (out0: t_Slice u8),
      (out1: t_Slice u8),
      (s:
        Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
          Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t) =
        Rust_primitives.Hax.Folds.fold_range (mk_usize 1)
          blocks
          (fun temp_0_ temp_1_ ->
              let
              (out0: t_Slice u8),
              (out1: t_Slice u8),
              (s:
                Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
                  Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t) =
                temp_0_
              in
              let _:usize = temp_1_ in
              ((Core_models.Slice.impl__len #u8 out0 <: usize) =. out0_len <: bool) &&
              ((Core_models.Slice.impl__len #u8 out1 <: usize) =. out1_len <: bool))
          (out0, out1, s
            <:
            (t_Slice u8 & t_Slice u8 &
              Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
                Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t))
          (fun temp_0_ i ->
              let
              (out0: t_Slice u8),
              (out1: t_Slice u8),
              (s:
                Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
                  Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t) =
                temp_0_
              in
              let i:usize = i in
              let _:Prims.unit =
                Libcrux_sha3.Proof_utils.Lemmas.lemma_mul_succ_le i blocks v_RATE
              in
              let s:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
                Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t =
                Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 (mk_usize 2)
                  #Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t
                  s
              in
              let (tmp0: t_Slice u8), (tmp1: t_Slice u8) =
                Libcrux_sha3.Traits.f_squeeze2 #(Libcrux_sha3.Generic_keccak.t_KeccakState
                      (mk_usize 2) Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t)
                  #Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t
                  #FStar.Tactics.Typeclasses.solve
                  v_RATE
                  s
                  out0
                  out1
                  (i *! v_RATE <: usize)
                  v_RATE
              in
              let out0:t_Slice u8 = tmp0 in
              let out1:t_Slice u8 = tmp1 in
              let _:Prims.unit = () in
              out0, out1, s
              <:
              (t_Slice u8 & t_Slice u8 &
                Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
                  Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t))
      in
      if last <. outlen
      then
        let s:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
          Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t =
          Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 (mk_usize 2)
            #Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t
            s
        in
        let (tmp0: t_Slice u8), (tmp1: t_Slice u8) =
          Libcrux_sha3.Traits.f_squeeze2 #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
                Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t)
            #Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t
            #FStar.Tactics.Typeclasses.solve
            v_RATE
            s
            out0
            out1
            last
            (outlen -! last <: usize)
        in
        let out0:t_Slice u8 = tmp0 in
        let out1:t_Slice u8 = tmp1 in
        let _:Prims.unit = () in
        out0, out1, s
        <:
        (t_Slice u8 & t_Slice u8 &
          Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
            Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t)
      else
        out0, out1, s
        <:
        (t_Slice u8 & t_Slice u8 &
          Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
            Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t)
  in
  out0, out1 <: (t_Slice u8 & t_Slice u8)

#pop-options

let keccak2
      (v_RATE: usize)
      (v_DELIM: u8)
      (data: t_Array (t_Slice u8) (mk_usize 2))
      (out0 out1: t_Slice u8)
    : Prims.Pure (t_Slice u8 & t_Slice u8)
      (requires
        Libcrux_sha3.Proof_utils.valid_rate v_RATE &&
        (Core_models.Slice.impl__len #u8 out0 <: usize) =.
        (Core_models.Slice.impl__len #u8 out1 <: usize) &&
        (Core_models.Slice.impl__len #u8 (data.[ mk_usize 0 ] <: t_Slice u8) <: usize) =.
        (Core_models.Slice.impl__len #u8 (data.[ mk_usize 1 ] <: t_Slice u8) <: usize))
      (ensures
        fun temp_0_ ->
          let (out0_future: t_Slice u8), (out1_future: t_Slice u8) = temp_0_ in
          (Core_models.Slice.impl__len #u8 out0_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out0 <: usize) &&
          (Core_models.Slice.impl__len #u8 out1_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out1 <: usize)) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core_models.Slice.impl__len #u8 out0 <: usize) =.
            (Core_models.Slice.impl__len #u8 out1 <: usize)
            <:
            bool)
      in
      ()
  in
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core_models.Slice.impl__len #u8 (data.[ mk_usize 0 ] <: t_Slice u8)
              <:
              usize) =.
            (Core_models.Slice.impl__len #u8 (data.[ mk_usize 1 ] <: t_Slice u8) <: usize)
            <:
            bool)
      in
      ()
  in
  let s:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
    Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t =
    absorb2 v_RATE v_DELIM data
  in
  let (tmp0: t_Slice u8), (tmp1: t_Slice u8) = squeeze2 v_RATE s out0 out1 in
  let out0:t_Slice u8 = tmp0 in
  let out1:t_Slice u8 = tmp1 in
  let _:Prims.unit = () in
  out0, out1 <: (t_Slice u8 & t_Slice u8)

let impl__squeeze_next_block
      (v_RATE: usize)
      (self:
          Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
            Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t)
      (out0 out1: t_Slice u8)
      (start: usize)
    : Prims.Pure
      (Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
          Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t &
        t_Slice u8 &
        t_Slice u8)
      (requires
        Libcrux_sha3.Proof_utils.valid_rate v_RATE &&
        ((Rust_primitives.Hax.Int.from_machine start <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine v_RATE <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine (Core_models.Slice.impl__len #u8 out0 <: usize)
          <:
          Hax_lib.Int.t_Int) &&
        (Core_models.Slice.impl__len #u8 out0 <: usize) =.
        (Core_models.Slice.impl__len #u8 out1 <: usize))
      (ensures
        fun temp_0_ ->
          let
          (self_e_future:
            Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
              Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t),
          (out0_future: t_Slice u8),
          (out1_future: t_Slice u8) =
            temp_0_
          in
          (Core_models.Slice.impl__len #u8 out0_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out0 <: usize) &&
          (Core_models.Slice.impl__len #u8 out1_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out1 <: usize)) =
  let self:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
    Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t =
    Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 (mk_usize 2)
      #Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t
      self
  in
  let (tmp0: t_Slice u8), (tmp1: t_Slice u8) =
    Libcrux_sha3.Traits.f_squeeze2 #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
          Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t)
      #Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t
      #FStar.Tactics.Typeclasses.solve
      v_RATE
      self
      out0
      out1
      start
      v_RATE
  in
  let out0:t_Slice u8 = tmp0 in
  let out1:t_Slice u8 = tmp1 in
  let _:Prims.unit = () in
  self, out0, out1
  <:
  (Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
      Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t &
    t_Slice u8 &
    t_Slice u8)

/// Write out the first block of Keccak output.
/// This function MUST NOT be called after any of the other `squeeze_*`
/// functions have been called, since that would result in a duplicate output
/// block.
let impl__squeeze_first_block
      (v_RATE: usize)
      (self:
          Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
            Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t)
      (out0 out1: t_Slice u8)
    : Prims.Pure (t_Slice u8 & t_Slice u8)
      (requires
        Libcrux_sha3.Proof_utils.valid_rate v_RATE &&
        v_RATE <=. (Core_models.Slice.impl__len #u8 out0 <: usize) &&
        (Core_models.Slice.impl__len #u8 out0 <: usize) =.
        (Core_models.Slice.impl__len #u8 out1 <: usize))
      (ensures
        fun temp_0_ ->
          let (out0_future: t_Slice u8), (out1_future: t_Slice u8) = temp_0_ in
          (Core_models.Slice.impl__len #u8 out0_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out0 <: usize) &&
          (Core_models.Slice.impl__len #u8 out1_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out1 <: usize)) =
  let (tmp0: t_Slice u8), (tmp1: t_Slice u8) =
    Libcrux_sha3.Traits.f_squeeze2 #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
          Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t)
      #Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t
      #FStar.Tactics.Typeclasses.solve
      v_RATE
      self
      out0
      out1
      (mk_usize 0)
      v_RATE
  in
  let out0:t_Slice u8 = tmp0 in
  let out1:t_Slice u8 = tmp1 in
  let _:Prims.unit = () in
  out0, out1 <: (t_Slice u8 & t_Slice u8)

let impl__squeeze_first_three_blocks
      (v_RATE: usize)
      (self:
          Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
            Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t)
      (out0 out1: t_Slice u8)
    : Prims.Pure
      (Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
          Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t &
        t_Slice u8 &
        t_Slice u8)
      (requires
        Libcrux_sha3.Proof_utils.valid_rate v_RATE &&
        (mk_usize 3 *! v_RATE <: usize) <=. (Core_models.Slice.impl__len #u8 out0 <: usize) &&
        (Core_models.Slice.impl__len #u8 out0 <: usize) =.
        (Core_models.Slice.impl__len #u8 out1 <: usize))
      (ensures
        fun temp_0_ ->
          let
          (self_e_future:
            Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
              Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t),
          (out0_future: t_Slice u8),
          (out1_future: t_Slice u8) =
            temp_0_
          in
          (Core_models.Slice.impl__len #u8 out0_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out0 <: usize) &&
          (Core_models.Slice.impl__len #u8 out1_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out1 <: usize)) =
  let (tmp0: t_Slice u8), (tmp1: t_Slice u8) =
    Libcrux_sha3.Traits.f_squeeze2 #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
          Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t)
      #Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t
      #FStar.Tactics.Typeclasses.solve
      v_RATE
      self
      out0
      out1
      (mk_usize 0)
      v_RATE
  in
  let out0:t_Slice u8 = tmp0 in
  let out1:t_Slice u8 = tmp1 in
  let _:Prims.unit = () in
  let self:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
    Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t =
    Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 (mk_usize 2)
      #Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t
      self
  in
  let (tmp0: t_Slice u8), (tmp1: t_Slice u8) =
    Libcrux_sha3.Traits.f_squeeze2 #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
          Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t)
      #Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t
      #FStar.Tactics.Typeclasses.solve
      v_RATE
      self
      out0
      out1
      v_RATE
      v_RATE
  in
  let out0:t_Slice u8 = tmp0 in
  let out1:t_Slice u8 = tmp1 in
  let _:Prims.unit = () in
  let self:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
    Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t =
    Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 (mk_usize 2)
      #Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t
      self
  in
  let (tmp0: t_Slice u8), (tmp1: t_Slice u8) =
    Libcrux_sha3.Traits.f_squeeze2 #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
          Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t)
      #Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t
      #FStar.Tactics.Typeclasses.solve
      v_RATE
      self
      out0
      out1
      (mk_usize 2 *! v_RATE <: usize)
      v_RATE
  in
  let out0:t_Slice u8 = tmp0 in
  let out1:t_Slice u8 = tmp1 in
  let _:Prims.unit = () in
  self, out0, out1
  <:
  (Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
      Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t &
    t_Slice u8 &
    t_Slice u8)

let impl__squeeze_first_five_blocks
      (v_RATE: usize)
      (self:
          Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
            Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t)
      (out0 out1: t_Slice u8)
    : Prims.Pure
      (Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
          Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t &
        t_Slice u8 &
        t_Slice u8)
      (requires
        Libcrux_sha3.Proof_utils.valid_rate v_RATE &&
        (mk_usize 5 *! v_RATE <: usize) <=. (Core_models.Slice.impl__len #u8 out0 <: usize) &&
        (Core_models.Slice.impl__len #u8 out0 <: usize) =.
        (Core_models.Slice.impl__len #u8 out1 <: usize))
      (ensures
        fun temp_0_ ->
          let
          (self_e_future:
            Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
              Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t),
          (out0_future: t_Slice u8),
          (out1_future: t_Slice u8) =
            temp_0_
          in
          (Core_models.Slice.impl__len #u8 out0_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out0 <: usize) &&
          (Core_models.Slice.impl__len #u8 out1_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out1 <: usize)) =
  let (tmp0: t_Slice u8), (tmp1: t_Slice u8) =
    Libcrux_sha3.Traits.f_squeeze2 #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
          Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t)
      #Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t
      #FStar.Tactics.Typeclasses.solve
      v_RATE
      self
      out0
      out1
      (mk_usize 0)
      v_RATE
  in
  let out0:t_Slice u8 = tmp0 in
  let out1:t_Slice u8 = tmp1 in
  let _:Prims.unit = () in
  let self:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
    Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t =
    Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 (mk_usize 2)
      #Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t
      self
  in
  let (tmp0: t_Slice u8), (tmp1: t_Slice u8) =
    Libcrux_sha3.Traits.f_squeeze2 #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
          Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t)
      #Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t
      #FStar.Tactics.Typeclasses.solve
      v_RATE
      self
      out0
      out1
      v_RATE
      v_RATE
  in
  let out0:t_Slice u8 = tmp0 in
  let out1:t_Slice u8 = tmp1 in
  let _:Prims.unit = () in
  let self:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
    Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t =
    Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 (mk_usize 2)
      #Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t
      self
  in
  let (tmp0: t_Slice u8), (tmp1: t_Slice u8) =
    Libcrux_sha3.Traits.f_squeeze2 #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
          Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t)
      #Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t
      #FStar.Tactics.Typeclasses.solve
      v_RATE
      self
      out0
      out1
      (mk_usize 2 *! v_RATE <: usize)
      v_RATE
  in
  let out0:t_Slice u8 = tmp0 in
  let out1:t_Slice u8 = tmp1 in
  let _:Prims.unit = () in
  let self:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
    Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t =
    Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 (mk_usize 2)
      #Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t
      self
  in
  let (tmp0: t_Slice u8), (tmp1: t_Slice u8) =
    Libcrux_sha3.Traits.f_squeeze2 #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
          Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t)
      #Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t
      #FStar.Tactics.Typeclasses.solve
      v_RATE
      self
      out0
      out1
      (mk_usize 3 *! v_RATE <: usize)
      v_RATE
  in
  let out0:t_Slice u8 = tmp0 in
  let out1:t_Slice u8 = tmp1 in
  let _:Prims.unit = () in
  let self:Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
    Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t =
    Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 (mk_usize 2)
      #Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t
      self
  in
  let (tmp0: t_Slice u8), (tmp1: t_Slice u8) =
    Libcrux_sha3.Traits.f_squeeze2 #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
          Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t)
      #Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t
      #FStar.Tactics.Typeclasses.solve
      v_RATE
      self
      out0
      out1
      (mk_usize 4 *! v_RATE <: usize)
      v_RATE
  in
  let out0:t_Slice u8 = tmp0 in
  let out1:t_Slice u8 = tmp1 in
  let _:Prims.unit = () in
  self, out0, out1
  <:
  (Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2)
      Libcrux_intrinsics.Arm64_extract.t_e_uint64x2_t &
    t_Slice u8 &
    t_Slice u8)
