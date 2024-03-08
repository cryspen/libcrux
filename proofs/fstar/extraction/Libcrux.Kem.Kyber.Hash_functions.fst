module Libcrux.Kem.Kyber.Hash_functions
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_G (input: t_Slice u8) = Libcrux.Digest.sha3_512_ input

let v_H (input: t_Slice u8) = Libcrux.Digest.sha3_256_ input

let v_PRF (v_LEN: usize) (input: t_Slice u8) = Libcrux.Digest.shake256 v_LEN input

let impl__new (v_K: usize) (_: Prims.unit) =
  {
    f_state
    =
    Core.Array.from_fn v_K
      (fun temp_0_ ->
          let _:usize = temp_0_ in
          Libcrux.Hacl.Sha3.Incremental.impl__Shake128State__new ()
          <:
          Libcrux.Hacl.Sha3.Incremental.t_Shake128State)
  }
  <:
  t_Shake128State v_K

let absorb (v_K: usize) (input: t_Array (t_Array u8 (sz 34)) v_K) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if ~.((v_K =. sz 2 <: bool) || (v_K =. sz 3 <: bool) || (v_K =. sz 4 <: bool))
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: K == 2 || K == 3 || K == 4"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let states:t_Shake128State v_K = impl__new v_K () in
  let states:t_Shake128State v_K =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      states
      (fun states i ->
          let states:t_Shake128State v_K = states in
          let i:usize = i in
          {
            states with
            f_state
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize states.f_state
              i
              (Libcrux.Hacl.Sha3.Incremental.impl__Shake128State__absorb_final (states.f_state.[ i ]
                    <:
                    Libcrux.Hacl.Sha3.Incremental.t_Shake128State)
                  (Rust_primitives.unsize (input.[ i ] <: t_Array u8 (sz 34)) <: t_Slice u8)
                <:
                Libcrux.Hacl.Sha3.Incremental.t_Shake128State)
            <:
            t_Array Libcrux.Hacl.Sha3.Incremental.t_Shake128State v_K
          }
          <:
          t_Shake128State v_K)
  in
  states

let free (v_K: usize) (xof_state: t_Shake128State v_K) =
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
        let xof_state:t_Shake128State v_K = xof_state in
        let i:usize = i in
        {
          xof_state with
          f_state
          =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize xof_state.f_state
            i
            (Libcrux.Hacl.Sha3.Incremental.impl__Shake128State__free (xof_state.f_state.[ i ]
                  <:
                  Libcrux.Hacl.Sha3.Incremental.t_Shake128State)
              <:
              Libcrux.Hacl.Sha3.Incremental.t_Shake128State)
          <:
          t_Array Libcrux.Hacl.Sha3.Incremental.t_Shake128State v_K
        }
        <:
        t_Shake128State v_K)

let squeeze_block (v_K: usize) (xof_state: t_Shake128State v_K) =
  let out:t_Array (t_Array u8 (sz 168)) v_K =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat 0uy (sz 168) <: t_Array u8 (sz 168)) v_K
  in
  let out, xof_state:(t_Array (t_Array u8 (sz 168)) v_K & t_Shake128State v_K) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      (out, xof_state <: (t_Array (t_Array u8 (sz 168)) v_K & t_Shake128State v_K))
      (fun temp_0_ i ->
          let out, xof_state:(t_Array (t_Array u8 (sz 168)) v_K & t_Shake128State v_K) = temp_0_ in
          let i:usize = i in
          let tmp0, out1:(Libcrux.Hacl.Sha3.Incremental.t_Shake128State & t_Array u8 (sz 168)) =
            Libcrux.Hacl.Sha3.Incremental.impl__Shake128State__squeeze_nblocks (sz 168)
              (xof_state.f_state.[ i ] <: Libcrux.Hacl.Sha3.Incremental.t_Shake128State)
          in
          let xof_state:t_Shake128State v_K =
            {
              xof_state with
              f_state
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize xof_state.f_state i tmp0
            }
            <:
            t_Shake128State v_K
          in
          let hoist1:t_Array u8 (sz 168) = out1 in
          let hoist2:t_Array (t_Array u8 (sz 168)) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out i hoist1
          in
          hoist2, xof_state <: (t_Array (t_Array u8 (sz 168)) v_K & t_Shake128State v_K))
  in
  let hax_temp_output:t_Array (t_Array u8 (sz 168)) v_K = out in
  xof_state, hax_temp_output <: (t_Shake128State v_K & t_Array (t_Array u8 (sz 168)) v_K)

let squeeze_three_blocks (v_K: usize) (xof_state: t_Shake128State v_K) =
  let out:t_Array (t_Array u8 (sz 504)) v_K =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat 0uy (sz 504) <: t_Array u8 (sz 504)) v_K
  in
  let out, xof_state:(t_Array (t_Array u8 (sz 504)) v_K & t_Shake128State v_K) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      (out, xof_state <: (t_Array (t_Array u8 (sz 504)) v_K & t_Shake128State v_K))
      (fun temp_0_ i ->
          let out, xof_state:(t_Array (t_Array u8 (sz 504)) v_K & t_Shake128State v_K) = temp_0_ in
          let i:usize = i in
          let tmp0, out1:(Libcrux.Hacl.Sha3.Incremental.t_Shake128State & t_Array u8 (sz 504)) =
            Libcrux.Hacl.Sha3.Incremental.impl__Shake128State__squeeze_nblocks (sz 504)
              (xof_state.f_state.[ i ] <: Libcrux.Hacl.Sha3.Incremental.t_Shake128State)
          in
          let xof_state:t_Shake128State v_K =
            {
              xof_state with
              f_state
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize xof_state.f_state i tmp0
            }
            <:
            t_Shake128State v_K
          in
          let hoist3:t_Array u8 (sz 504) = out1 in
          let hoist4:t_Array (t_Array u8 (sz 504)) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out i hoist3
          in
          hoist4, xof_state <: (t_Array (t_Array u8 (sz 504)) v_K & t_Shake128State v_K))
  in
  let hax_temp_output:t_Array (t_Array u8 (sz 504)) v_K = out in
  xof_state, hax_temp_output <: (t_Shake128State v_K & t_Array (t_Array u8 (sz 504)) v_K)
