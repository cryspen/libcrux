module Libcrux.Kem.Kyber.Hash_functions
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_G (input: t_Slice u8) = Libcrux.Digest.sha3_512_ input

let v_H (input: t_Slice u8) = Libcrux.Digest.sha3_256_ input

let v_PRF (v_LEN: usize) (input: t_Slice u8) = Libcrux.Digest.shake256 v_LEN input

let v_XOF_absorb (v_K: usize) (input: t_Array (t_Array u8 (sz 34)) v_K) =
  let (state: t_Array Libcrux.Digest.t_Shake128State v_K):t_Array Libcrux.Digest.t_Shake128State v_K
  =
    Core.Array.from_fn v_K
      (fun temp_0_ ->
          let _:usize = temp_0_ in
          Libcrux.Digest.shake128_init () <: Libcrux.Digest.t_Shake128State)
  in
  let state:t_Array Libcrux.Digest.t_Shake128State v_K =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      state
      (fun state i ->
          let state:t_Array Libcrux.Digest.t_Shake128State v_K = state in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize state
            i
            (Libcrux.Digest.shake128_absorb_final (state.[ i ] <: Libcrux.Digest.t_Shake128State)
                (Rust_primitives.unsize (input.[ i ] <: t_Array u8 (sz 34)) <: t_Slice u8)
              <:
              Libcrux.Digest.t_Shake128State)
          <:
          t_Array Libcrux.Digest.t_Shake128State v_K)
  in
  state

let v_XOF_free (v_K: usize) (xof_state: t_Array Libcrux.Digest.t_Shake128State v_K) =
  Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
            Core.Ops.Range.f_start = sz 0;
            Core.Ops.Range.f_end = v_K
          }
          <:
          Core.Ops.Range.t_Range usize)
      <:
      Core.Ops.Range.t_Range usize)
    xof_state
    (fun xof_state i ->
        let xof_state:t_Array Libcrux.Digest.t_Shake128State v_K = xof_state in
        let i:usize = i in
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize xof_state
          i
          (Libcrux.Digest.impl__Shake128State__free (xof_state.[ i ]
                <:
                Libcrux.Digest.t_Shake128State)
            <:
            Libcrux.Digest.t_Shake128State)
        <:
        t_Array Libcrux.Digest.t_Shake128State v_K)

let v_XOF_squeeze_block (v_K: usize) (xof_state: t_Array Libcrux.Digest.t_Shake128State v_K) =
  let output:t_Array (t_Array u8 (sz 168)) v_K =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat 0uy (sz 168) <: t_Array u8 (sz 168)) v_K
  in
  let output, xof_state:(t_Array (t_Array u8 (sz 168)) v_K &
    t_Array Libcrux.Digest.t_Shake128State v_K) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      (output, xof_state
        <:
        (t_Array (t_Array u8 (sz 168)) v_K & t_Array Libcrux.Digest.t_Shake128State v_K))
      (fun temp_0_ i ->
          let output, xof_state:(t_Array (t_Array u8 (sz 168)) v_K &
            t_Array Libcrux.Digest.t_Shake128State v_K) =
            temp_0_
          in
          let i:usize = i in
          let tmp0, out:(Libcrux.Digest.t_Shake128State & t_Array u8 (sz 168)) =
            Libcrux.Digest.shake128_squeeze_nblocks (sz 168)
              (xof_state.[ i ] <: Libcrux.Digest.t_Shake128State)
          in
          let xof_state:t_Array Libcrux.Digest.t_Shake128State v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize xof_state i tmp0
          in
          let hoist1:t_Array u8 (sz 168) = out in
          let hoist2:t_Array (t_Array u8 (sz 168)) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize output i hoist1
          in
          hoist2, xof_state
          <:
          (t_Array (t_Array u8 (sz 168)) v_K & t_Array Libcrux.Digest.t_Shake128State v_K))
  in
  output, xof_state
  <:
  (t_Array (t_Array u8 (sz 168)) v_K & t_Array Libcrux.Digest.t_Shake128State v_K)

let v_XOF_squeeze_three_blocks (v_K: usize) (xof_state: t_Array Libcrux.Digest.t_Shake128State v_K) =
  let output:t_Array (t_Array u8 (sz 504)) v_K =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat 0uy (sz 504) <: t_Array u8 (sz 504)) v_K
  in
  let output, xof_state:(t_Array (t_Array u8 (sz 504)) v_K &
    t_Array Libcrux.Digest.t_Shake128State v_K) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      (output, xof_state
        <:
        (t_Array (t_Array u8 (sz 504)) v_K & t_Array Libcrux.Digest.t_Shake128State v_K))
      (fun temp_0_ i ->
          let output, xof_state:(t_Array (t_Array u8 (sz 504)) v_K &
            t_Array Libcrux.Digest.t_Shake128State v_K) =
            temp_0_
          in
          let i:usize = i in
          let tmp0, out:(Libcrux.Digest.t_Shake128State & t_Array u8 (sz 504)) =
            Libcrux.Digest.shake128_squeeze_nblocks (sz 504)
              (xof_state.[ i ] <: Libcrux.Digest.t_Shake128State)
          in
          let xof_state:t_Array Libcrux.Digest.t_Shake128State v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize xof_state i tmp0
          in
          let hoist3:t_Array u8 (sz 504) = out in
          let hoist4:t_Array (t_Array u8 (sz 504)) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize output i hoist3
          in
          hoist4, xof_state
          <:
          (t_Array (t_Array u8 (sz 504)) v_K & t_Array Libcrux.Digest.t_Shake128State v_K))
  in
  output, xof_state
  <:
  (t_Array (t_Array u8 (sz 504)) v_K & t_Array Libcrux.Digest.t_Shake128State v_K)
