module Hacspec_sha3.Sponge
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// Map byte-lane index `l` to the flat state array index.
/// FIPS 202 Section 3.1.2 defines how a bit string maps onto the state array.
/// In the byte-oriented convention used by the reference implementation,
/// byte-lane `l` maps to `A[l % 5, l / 5]` = `state[5*(l%5) + l/5]`.
let lane_index (l: usize) : Prims.Pure usize (requires l <. mk_usize 25) (fun _ -> Prims.l_True) =
  (mk_usize 5 *! (l %! mk_usize 5 <: usize) <: usize) +! (l /! mk_usize 5 <: usize)

/// XOR a block of message bytes into the state (little-endian, lane-interleaved).
/// Corresponds to the `S ⊕ (Pi || 0^c)` step of Algorithm 8.
let xor_block_into_state (state: t_Array u64 (mk_usize 25)) (block: t_Slice u8) (rate: usize)
    : Prims.Pure (t_Array u64 (mk_usize 25))
      (requires
        rate <=. mk_usize 200 && (rate %! mk_usize 8 <: usize) =. mk_usize 0 &&
        (Core_models.Slice.impl__len #u8 block <: usize) >=. rate)
      (fun _ -> Prims.l_True) =
  let state:t_Array u64 (mk_usize 25) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (rate /! mk_usize 8 <: usize)
      (fun state temp_1_ ->
          let state:t_Array u64 (mk_usize 25) = state in
          let _:usize = temp_1_ in
          true)
      state
      (fun state i ->
          let state:t_Array u64 (mk_usize 25) = state in
          let i:usize = i in
          let offset:usize = mk_usize 8 *! i in
          let lane_val:u64 =
            Core_models.Num.impl_u64__from_le_bytes (let list =
                  [
                    block.[ offset ] <: u8;
                    block.[ offset +! mk_usize 1 <: usize ] <: u8;
                    block.[ offset +! mk_usize 2 <: usize ] <: u8;
                    block.[ offset +! mk_usize 3 <: usize ] <: u8;
                    block.[ offset +! mk_usize 4 <: usize ] <: u8;
                    block.[ offset +! mk_usize 5 <: usize ] <: u8;
                    block.[ offset +! mk_usize 6 <: usize ] <: u8;
                    block.[ offset +! mk_usize 7 <: usize ] <: u8
                  ]
                in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
                Rust_primitives.Hax.array_of_list 8 list)
          in
          let idx:usize = lane_index i in
          let state:t_Array u64 (mk_usize 25) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize state
              idx
              ((state.[ idx ] <: u64) ^. lane_val <: u64)
          in
          state)
  in
  state

#push-options "--z3rlimit 500"

/// Extract `len` bytes from the rate portion of the state (little-endian, lane-interleaved).
/// Corresponds to `Trunc_r(S)` in Algorithm 8.
let squeeze_state (state: t_Array u64 (mk_usize 25)) (output: t_Slice u8) (out_offset len: usize)
    : Prims.Pure (t_Slice u8)
      (requires
        len <=. mk_usize 200 && (Core_models.Slice.impl__len #u8 output <: usize) >=. len &&
        out_offset <=. ((Core_models.Slice.impl__len #u8 output <: usize) -! len <: usize))
      (ensures
        fun output_future ->
          let output_future:t_Slice u8 = output_future in
          (Core_models.Slice.impl__len #u8 output_future <: usize) =.
          (Core_models.Slice.impl__len #u8 output <: usize)) =
  let e_orig_len:usize = Core_models.Slice.impl__len #u8 output in
  let full_lanes:usize = len /! mk_usize 8 in
  let output:t_Slice u8 =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      full_lanes
      (fun output i ->
          let output:t_Slice u8 = output in
          let i:usize = i in
          (Core_models.Slice.impl__len #u8 output <: usize) =. e_orig_len <: bool)
      output
      (fun output i ->
          let output:t_Slice u8 = output in
          let i:usize = i in
          let idx:usize = lane_index i in
          let bytes:t_Array u8 (mk_usize 8) =
            Core_models.Num.impl_u64__to_le_bytes (state.[ idx ] <: u64)
          in
          Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
            (mk_usize 8)
            (fun output b ->
                let output:t_Slice u8 = output in
                let b:usize = b in
                (Core_models.Slice.impl__len #u8 output <: usize) =. e_orig_len <: bool)
            output
            (fun output b ->
                let output:t_Slice u8 = output in
                let b:usize = b in
                let output:t_Slice u8 =
                  Rust_primitives.Hax.Monomorphized_update_at.update_at_usize output
                    ((out_offset +! (mk_usize 8 *! i <: usize) <: usize) +! b <: usize)
                    (bytes.[ b ] <: u8)
                in
                output))
  in
  let remaining:usize = len %! mk_usize 8 in
  let output:t_Slice u8 =
    if remaining >. mk_usize 0
    then
      let idx:usize = lane_index full_lanes in
      let bytes:t_Array u8 (mk_usize 8) =
        Core_models.Num.impl_u64__to_le_bytes (state.[ idx ] <: u64)
      in
      Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
        remaining
        (fun output b ->
            let output:t_Slice u8 = output in
            let b:usize = b in
            (Core_models.Slice.impl__len #u8 output <: usize) =. e_orig_len <: bool)
        output
        (fun output b ->
            let output:t_Slice u8 = output in
            let b:usize = b in
            let output:t_Slice u8 =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize output
                ((out_offset +! (mk_usize 8 *! full_lanes <: usize) <: usize) +! b <: usize)
                (bytes.[ b ] <: u8)
            in
            output)
    else output
  in
  output

#pop-options

#push-options "--z3rlimit 500"

/// Keccak sponge — FIPS 202, Algorithm 8 combined with pad10*1 (Algorithm 9).
/// 1. Absorb: split `message` into `rate`-byte blocks, XOR each into the
///    state, and apply Keccak-f. The final partial block is padded with
///    the domain separation byte `delim` and the pad10*1 terminator `0x80`.
/// 2. Squeeze: extract `OUTPUT_LEN` bytes from the state, applying
///    Keccak-f between each `rate`-byte block of output.
/// The `OUTPUT_LEN < usize::MAX - 200` precondition is a Rust implementation
/// artifact to prevent arithmetic overflow; FIPS 202 places no upper bound
/// on the output length.
let keccak (v_OUTPUT_LEN rate: usize) (delim: u8) (message: t_Slice u8)
    : Prims.Pure (t_Array u8 v_OUTPUT_LEN)
      (requires
        rate >. mk_usize 0 && rate <=. mk_usize 200 && (rate %! mk_usize 8 <: usize) =. mk_usize 0 &&
        v_OUTPUT_LEN <. (Core_models.Num.impl_usize__MAX -! mk_usize 200 <: usize))
      (fun _ -> Prims.l_True) =
  let (state: t_Array u64 (mk_usize 25)):t_Array u64 (mk_usize 25) =
    Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 25)
  in
  let num_full_blocks:usize = (Core_models.Slice.impl__len #u8 message <: usize) /! rate in
  let state:t_Array u64 (mk_usize 25) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      num_full_blocks
      (fun state temp_1_ ->
          let state:t_Array u64 (mk_usize 25) = state in
          let _:usize = temp_1_ in
          true)
      state
      (fun state block_idx ->
          let state:t_Array u64 (mk_usize 25) = state in
          let block_idx:usize = block_idx in
          let offset:usize = block_idx *! rate in
          let state:t_Array u64 (mk_usize 25) =
            xor_block_into_state state
              (message.[ {
                    Core_models.Ops.Range.f_start = offset;
                    Core_models.Ops.Range.f_end = offset +! rate <: usize
                  }
                  <:
                  Core_models.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
              rate
          in
          let state:t_Array u64 (mk_usize 25) = Hacspec_sha3.Keccak_f.keccak_f state in
          state)
  in
  let last_block:t_Array u8 (mk_usize 200) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 200) in
  let remaining:usize =
    (Core_models.Slice.impl__len #u8 message <: usize) -! (num_full_blocks *! rate <: usize)
  in
  let last_block:t_Array u8 (mk_usize 200) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      remaining
      (fun last_block temp_1_ ->
          let last_block:t_Array u8 (mk_usize 200) = last_block in
          let _:usize = temp_1_ in
          true)
      last_block
      (fun last_block i ->
          let last_block:t_Array u8 (mk_usize 200) = last_block in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize last_block
            i
            (message.[ (num_full_blocks *! rate <: usize) +! i <: usize ] <: u8)
          <:
          t_Array u8 (mk_usize 200))
  in
  let last_block:t_Array u8 (mk_usize 200) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize last_block remaining delim
  in
  let last_block:t_Array u8 (mk_usize 200) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize last_block
      (rate -! mk_usize 1 <: usize)
      ((last_block.[ rate -! mk_usize 1 <: usize ] <: u8) |. mk_u8 128 <: u8)
  in
  let state:t_Array u64 (mk_usize 25) =
    xor_block_into_state state (last_block <: t_Slice u8) rate
  in
  let state:t_Array u64 (mk_usize 25) = Hacspec_sha3.Keccak_f.keccak_f state in
  let output:t_Array u8 v_OUTPUT_LEN = Rust_primitives.Hax.repeat (mk_u8 0) v_OUTPUT_LEN in
  let offset:usize = mk_usize 0 in
  let (offset: usize), (output: t_Array u8 v_OUTPUT_LEN), (state: t_Array u64 (mk_usize 25)) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (((v_OUTPUT_LEN +! rate <: usize) -! mk_usize 1 <: usize) /! rate <: usize)
      (fun temp_0_ e_squeeze_round ->
          let (offset: usize), (output: t_Array u8 v_OUTPUT_LEN), (state: t_Array u64 (mk_usize 25))
          =
            temp_0_
          in
          let e_squeeze_round:usize = e_squeeze_round in
          offset <=. v_OUTPUT_LEN <: bool)
      (offset, output, state <: (usize & t_Array u8 v_OUTPUT_LEN & t_Array u64 (mk_usize 25)))
      (fun temp_0_ e_squeeze_round ->
          let (offset: usize), (output: t_Array u8 v_OUTPUT_LEN), (state: t_Array u64 (mk_usize 25))
          =
            temp_0_
          in
          let e_squeeze_round:usize = e_squeeze_round in
          let to_copy:usize =
            if (v_OUTPUT_LEN -! offset <: usize) <. rate then v_OUTPUT_LEN -! offset else rate
          in
          let output:t_Array u8 v_OUTPUT_LEN = squeeze_state state output offset to_copy in
          let offset:usize = offset +! to_copy in
          if offset <. v_OUTPUT_LEN
          then
            let state:t_Array u64 (mk_usize 25) = Hacspec_sha3.Keccak_f.keccak_f state in
            offset, output, state <: (usize & t_Array u8 v_OUTPUT_LEN & t_Array u64 (mk_usize 25))
          else
            offset, output, state <: (usize & t_Array u8 v_OUTPUT_LEN & t_Array u64 (mk_usize 25)))
  in
  output

#pop-options
