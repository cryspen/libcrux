module Libcrux.Kem.Kyber.Hash_functions
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_G (input: t_Slice u8) = Libcrux.Digest.sha3_512_ input

let v_H (input: t_Slice u8) = Libcrux.Digest.sha3_256_ input

let v_PRF (v_LEN: usize) (input: t_Slice u8) = Libcrux.Digest.shake256 v_LEN input

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
  let state:Libcrux.Digest.Incremental_x4.t_Shake128StateX4 =
    Libcrux.Digest.Incremental_x4.impl__Shake128StateX4__new ()
  in
  let (data: t_Array (t_Slice u8) v_K):t_Array (t_Slice u8) v_K =
    Rust_primitives.Hax.repeat (Rust_primitives.unsize (let list = [0uy] in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
            Rust_primitives.Hax.array_of_list 1 list)
        <:
        t_Slice u8)
      v_K
  in
  let data:t_Array (t_Slice u8) v_K =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = v_K }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      data
      (fun data i ->
          let data:t_Array (t_Slice u8) v_K = data in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize data
            i
            (Rust_primitives.unsize (input.[ i ] <: t_Array u8 (sz 34)) <: t_Slice u8)
          <:
          t_Array (t_Slice u8) v_K)
  in
  let state:Libcrux.Digest.Incremental_x4.t_Shake128StateX4 =
    Libcrux.Digest.Incremental_x4.impl__Shake128StateX4__absorb_final v_K state data
  in
  state

let free_state (xof_state: Libcrux.Digest.Incremental_x4.t_Shake128StateX4) =
  let _:Prims.unit = Libcrux.Digest.Incremental_x4.impl__Shake128StateX4__free_memory xof_state in
  ()

let squeeze_block (v_K: usize) (xof_state: Libcrux.Digest.Incremental_x4.t_Shake128StateX4) =
  let tmp0, out1:(Libcrux.Digest.Incremental_x4.t_Shake128StateX4 &
    t_Array (t_Array u8 (sz 168)) v_K) =
    Libcrux.Digest.Incremental_x4.impl__Shake128StateX4__squeeze_blocks (sz 168) v_K xof_state
  in
  let xof_state:Libcrux.Digest.Incremental_x4.t_Shake128StateX4 = tmp0 in
  let (output: t_Array (t_Array u8 (sz 168)) v_K):t_Array (t_Array u8 (sz 168)) v_K = out1 in
  let out:t_Array (t_Array u8 (sz 168)) v_K =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat 0uy (sz 168) <: t_Array u8 (sz 168)) v_K
  in
  let out:t_Array (t_Array u8 (sz 168)) v_K =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = v_K }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      out
      (fun out i ->
          let out:t_Array (t_Array u8 (sz 168)) v_K = out in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
            i
            (output.[ i ] <: t_Array u8 (sz 168))
          <:
          t_Array (t_Array u8 (sz 168)) v_K)
  in
  let hax_temp_output:t_Array (t_Array u8 (sz 168)) v_K = out in
  xof_state, hax_temp_output
  <:
  (Libcrux.Digest.Incremental_x4.t_Shake128StateX4 & t_Array (t_Array u8 (sz 168)) v_K)

let squeeze_three_blocks (v_K: usize) (xof_state: Libcrux.Digest.Incremental_x4.t_Shake128StateX4) =
  let tmp0, out1:(Libcrux.Digest.Incremental_x4.t_Shake128StateX4 &
    t_Array (t_Array u8 (sz 504)) v_K) =
    Libcrux.Digest.Incremental_x4.impl__Shake128StateX4__squeeze_blocks (sz 504) v_K xof_state
  in
  let xof_state:Libcrux.Digest.Incremental_x4.t_Shake128StateX4 = tmp0 in
  let (output: t_Array (t_Array u8 (sz 504)) v_K):t_Array (t_Array u8 (sz 504)) v_K = out1 in
  let out:t_Array (t_Array u8 (sz 504)) v_K =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat 0uy (sz 504) <: t_Array u8 (sz 504)) v_K
  in
  let out:t_Array (t_Array u8 (sz 504)) v_K =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = v_K }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      out
      (fun out i ->
          let out:t_Array (t_Array u8 (sz 504)) v_K = out in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
            i
            (output.[ i ] <: t_Array u8 (sz 504))
          <:
          t_Array (t_Array u8 (sz 504)) v_K)
  in
  let hax_temp_output:t_Array (t_Array u8 (sz 504)) v_K = out in
  xof_state, hax_temp_output
  <:
  (Libcrux.Digest.Incremental_x4.t_Shake128StateX4 & t_Array (t_Array u8 (sz 504)) v_K)
