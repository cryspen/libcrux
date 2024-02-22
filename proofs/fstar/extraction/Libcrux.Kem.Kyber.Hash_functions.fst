module Libcrux.Kem.Kyber.Hash_functions
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_G (input: t_Slice u8) = Libcrux.Digest.sha3_512_ input

let v_H (input: t_Slice u8) = Libcrux.Digest.sha3_256_ input

let v_PRF (v_LEN: usize) (input: t_Slice u8) = Libcrux.Digest.shake256 v_LEN input

let v_XOF_absorb (v_K: usize) (input: t_Array (t_Array u8 (sz 34)) v_K) =
  let (out_vec: Alloc.Vec.t_Vec Libcrux.Digest.t_Shake128State Alloc.Alloc.t_Global):Alloc.Vec.t_Vec
    Libcrux.Digest.t_Shake128State Alloc.Alloc.t_Global =
    Alloc.Vec.impl__new ()
  in
  let out_vec:Alloc.Vec.t_Vec Libcrux.Digest.t_Shake128State Alloc.Alloc.t_Global =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      out_vec
      (fun out_vec i ->
          let out_vec:Alloc.Vec.t_Vec Libcrux.Digest.t_Shake128State Alloc.Alloc.t_Global =
            out_vec
          in
          let i:usize = i in
          let st:Libcrux.Digest.t_Shake128State = Libcrux.Digest.shake128_init () in
          let st:Libcrux.Digest.t_Shake128State =
            Libcrux.Digest.shake128_absorb_final st
              (Rust_primitives.unsize (input.[ i ] <: t_Array u8 (sz 34)) <: t_Slice u8)
          in
          let out_vec:Alloc.Vec.t_Vec Libcrux.Digest.t_Shake128State Alloc.Alloc.t_Global =
            Alloc.Vec.impl_1__push out_vec st
          in
          out_vec)
  in
  let (states: t_Array Libcrux.Digest.t_Shake128State v_K):t_Array Libcrux.Digest.t_Shake128State
    v_K =
    Core.Result.impl__unwrap_or_else (Core.Convert.f_try_into out_vec
        <:
        Core.Result.t_Result (t_Array Libcrux.Digest.t_Shake128State v_K)
          (Alloc.Vec.t_Vec Libcrux.Digest.t_Shake128State Alloc.Alloc.t_Global))
      (fun temp_0_ ->
          let _:Alloc.Vec.t_Vec Libcrux.Digest.t_Shake128State Alloc.Alloc.t_Global = temp_0_ in
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "explicit panic"
              <:
              Rust_primitives.Hax.t_Never)
          <:
          t_Array Libcrux.Digest.t_Shake128State v_K)
  in
  { f_states = states } <: t_XofState v_K

let v_XOF_squeeze_block (v_K: usize) (xof_state: t_XofState v_K) =
  let (out: t_Array (t_Array u8 (sz 168)) v_K):t_Array (t_Array u8 (sz 168)) v_K =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat 0uy (sz 168) <: t_Array u8 (sz 168)) v_K
  in
  let out, xof_state:(t_Array (t_Array u8 (sz 168)) v_K & t_XofState v_K) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      (out, xof_state <: (t_Array (t_Array u8 (sz 168)) v_K & t_XofState v_K))
      (fun temp_0_ i ->
          let out, xof_state:(t_Array (t_Array u8 (sz 168)) v_K & t_XofState v_K) = temp_0_ in
          let i:usize = i in
          let tmp0, out:(Libcrux.Digest.t_Shake128State & t_Array u8 (sz 168)) =
            Libcrux.Digest.shake128_squeeze_nblocks (sz 168)
              (xof_state.f_states.[ i ] <: Libcrux.Digest.t_Shake128State)
          in
          let xof_state:t_XofState v_K =
            {
              xof_state with
              f_states
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize xof_state.f_states i tmp0
            }
            <:
            t_XofState v_K
          in
          let hoist21:t_Array u8 (sz 168) = out in
          let hoist22:t_Array (t_Array u8 (sz 168)) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out i hoist21
          in
          hoist22, xof_state <: (t_Array (t_Array u8 (sz 168)) v_K & t_XofState v_K))
  in
  let hax_temp_output:t_Array (t_Array u8 (sz 168)) v_K = out in
  xof_state, hax_temp_output <: (t_XofState v_K & t_Array (t_Array u8 (sz 168)) v_K)

let v_XOF_squeeze_three_blocks (v_K: usize) (xof_state: t_XofState v_K) =
  let out:t_Array (t_Array u8 (sz 504)) v_K =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat 0uy (sz 504) <: t_Array u8 (sz 504)) v_K
  in
  let out, xof_state:(t_Array (t_Array u8 (sz 504)) v_K & t_XofState v_K) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      (out, xof_state <: (t_Array (t_Array u8 (sz 504)) v_K & t_XofState v_K))
      (fun temp_0_ i ->
          let out, xof_state:(t_Array (t_Array u8 (sz 504)) v_K & t_XofState v_K) = temp_0_ in
          let i:usize = i in
          let tmp0, out:(Libcrux.Digest.t_Shake128State & t_Array u8 (sz 504)) =
            Libcrux.Digest.shake128_squeeze_nblocks (sz 504)
              (xof_state.f_states.[ i ] <: Libcrux.Digest.t_Shake128State)
          in
          let xof_state:t_XofState v_K =
            {
              xof_state with
              f_states
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize xof_state.f_states i tmp0
            }
            <:
            t_XofState v_K
          in
          let hoist23:t_Array u8 (sz 504) = out in
          let hoist24:t_Array (t_Array u8 (sz 504)) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out i hoist23
          in
          hoist24, xof_state <: (t_Array (t_Array u8 (sz 504)) v_K & t_XofState v_K))
  in
  let hax_temp_output:t_Array (t_Array u8 (sz 504)) v_K = out in
  xof_state, hax_temp_output <: (t_XofState v_K & t_Array (t_Array u8 (sz 504)) v_K)
