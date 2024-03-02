module Libcrux.Kem.Kyber.Hash_functions
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_G (input: t_Slice u8) = Libcrux.Digest.sha3_512_ input

let v_H (input: t_Slice u8) = Libcrux.Digest.sha3_256_ input

let v_PRF (v_LEN: usize) (input: t_Slice u8) = Libcrux.Digest.shake256 v_LEN input

let v_XOF_absorb (v_K: usize) (input: t_Array (t_Array u8 (sz 34)) v_K) =
  match cast (v_K <: usize) <: u8 with
  | 2uy ->
    let state:Libcrux.Digest.t_Shake128StateX2 = Libcrux.Digest.shake128_init_x2 () in
    let state:Libcrux.Digest.t_Shake128StateX2 =
      Libcrux.Digest.shake128_absorb_final_x2 state
        (Rust_primitives.unsize (input.[ sz 0 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
        (Rust_primitives.unsize (input.[ sz 1 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
    in
    XofState_X2 state <: t_XofState
  | 3uy ->
    let state:Libcrux.Digest.t_Shake128StateX3 = Libcrux.Digest.shake128_init_x3 () in
    let state:Libcrux.Digest.t_Shake128StateX3 =
      Libcrux.Digest.shake128_absorb_final_x3 state
        (Rust_primitives.unsize (input.[ sz 0 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
        (Rust_primitives.unsize (input.[ sz 1 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
        (Rust_primitives.unsize (input.[ sz 2 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
    in
    XofState_X3 state <: t_XofState
  | 4uy ->
    let state:Libcrux.Digest.t_Shake128StateX4 = Libcrux.Digest.shake128_init_x4 () in
    let state:Libcrux.Digest.t_Shake128StateX4 =
      Libcrux.Digest.shake128_absorb_final_x4 state
        (Rust_primitives.unsize (input.[ sz 0 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
        (Rust_primitives.unsize (input.[ sz 1 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
        (Rust_primitives.unsize (input.[ sz 2 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
        (Rust_primitives.unsize (input.[ sz 3 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
    in
    XofState_X4 state <: t_XofState
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

let v_XOF_free (v_K: usize) (xof_state: t_XofState) =
  match cast (v_K <: usize) <: u8 with
  | 2uy ->
    (match xof_state with
      | XofState_X2 st ->
        let _:Prims.unit = Libcrux.Digest.shake128_free_x2 st in
        ()
      | _ ->
        Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

            <:
            Rust_primitives.Hax.t_Never))
  | 3uy ->
    (match xof_state with
      | XofState_X3 st ->
        let _:Prims.unit = Libcrux.Digest.shake128_free_x3 st in
        ()
      | _ ->
        Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

            <:
            Rust_primitives.Hax.t_Never))
  | 4uy ->
    (match xof_state with
      | XofState_X4 st ->
        let _:Prims.unit = Libcrux.Digest.shake128_free_x4 st in
        ()
      | _ ->
        Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

            <:
            Rust_primitives.Hax.t_Never))
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

let v_XOF_squeeze_block (v_K: usize) (xof_state: t_XofState) =
  let output:t_Array (t_Array u8 (sz 168)) v_K =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat 0uy (sz 168) <: t_Array u8 (sz 168)) v_K
  in
  match cast (v_K <: usize) <: u8 with
  | 2uy ->
    (match xof_state with
      | XofState_X2 st ->
        let tmp0, out:(Libcrux.Digest.t_Shake128StateX2 & t_Array (t_Array u8 (sz 168)) (sz 2)) =
          Libcrux.Digest.shake128_squeeze_nblocks_x2 (sz 168) st
        in
        let st:Libcrux.Digest.t_Shake128StateX2 = tmp0 in
        let tmp:t_Array (t_Array u8 (sz 168)) (sz 2) = out in
        let output:t_Array (t_Array u8 (sz 168)) v_K =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize output
            (sz 0)
            (tmp.[ sz 0 ] <: t_Array u8 (sz 168))
        in
        let output:t_Array (t_Array u8 (sz 168)) v_K =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize output
            (sz 1)
            (tmp.[ sz 1 ] <: t_Array u8 (sz 168))
        in
        output, (XofState_X2 st <: t_XofState) <: (t_Array (t_Array u8 (sz 168)) v_K & t_XofState)
      | _ ->
        Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

            <:
            Rust_primitives.Hax.t_Never))
  | 3uy ->
    (match xof_state with
      | XofState_X3 st ->
        let tmp0, out:(Libcrux.Digest.t_Shake128StateX3 & t_Array (t_Array u8 (sz 168)) (sz 3)) =
          Libcrux.Digest.shake128_squeeze_nblocks_x3 (sz 168) st
        in
        let st:Libcrux.Digest.t_Shake128StateX3 = tmp0 in
        let tmp:t_Array (t_Array u8 (sz 168)) (sz 3) = out in
        let output:t_Array (t_Array u8 (sz 168)) v_K =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize output
            (sz 0)
            (tmp.[ sz 0 ] <: t_Array u8 (sz 168))
        in
        let output:t_Array (t_Array u8 (sz 168)) v_K =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize output
            (sz 1)
            (tmp.[ sz 1 ] <: t_Array u8 (sz 168))
        in
        let output:t_Array (t_Array u8 (sz 168)) v_K =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize output
            (sz 2)
            (tmp.[ sz 2 ] <: t_Array u8 (sz 168))
        in
        output, (XofState_X3 st <: t_XofState) <: (t_Array (t_Array u8 (sz 168)) v_K & t_XofState)
      | _ ->
        Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

            <:
            Rust_primitives.Hax.t_Never))
  | 4uy ->
    (match xof_state with
      | XofState_X4 st ->
        let tmp0, out:(Libcrux.Digest.t_Shake128StateX4 & t_Array (t_Array u8 (sz 168)) (sz 4)) =
          Libcrux.Digest.shake128_squeeze_nblocks_x4 (sz 168) st
        in
        let st:Libcrux.Digest.t_Shake128StateX4 = tmp0 in
        let tmp:t_Array (t_Array u8 (sz 168)) (sz 4) = out in
        let output:t_Array (t_Array u8 (sz 168)) v_K =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize output
            (sz 0)
            (tmp.[ sz 0 ] <: t_Array u8 (sz 168))
        in
        let output:t_Array (t_Array u8 (sz 168)) v_K =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize output
            (sz 1)
            (tmp.[ sz 1 ] <: t_Array u8 (sz 168))
        in
        let output:t_Array (t_Array u8 (sz 168)) v_K =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize output
            (sz 2)
            (tmp.[ sz 2 ] <: t_Array u8 (sz 168))
        in
        let output:t_Array (t_Array u8 (sz 168)) v_K =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize output
            (sz 3)
            (tmp.[ sz 3 ] <: t_Array u8 (sz 168))
        in
        output, (XofState_X4 st <: t_XofState) <: (t_Array (t_Array u8 (sz 168)) v_K & t_XofState)
      | _ ->
        Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

            <:
            Rust_primitives.Hax.t_Never))
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

let v_XOF_squeeze_three_blocks (v_K: usize) (xof_state: t_XofState) =
  let output:t_Array (t_Array u8 (sz 504)) v_K =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat 0uy (sz 504) <: t_Array u8 (sz 504)) v_K
  in
  match cast (v_K <: usize) <: u8 with
  | 2uy ->
    (match xof_state with
      | XofState_X2 st ->
        let tmp0, out:(Libcrux.Digest.t_Shake128StateX2 & t_Array (t_Array u8 (sz 504)) (sz 2)) =
          Libcrux.Digest.shake128_squeeze_nblocks_x2 (sz 504) st
        in
        let st:Libcrux.Digest.t_Shake128StateX2 = tmp0 in
        let tmp:t_Array (t_Array u8 (sz 504)) (sz 2) = out in
        let output:t_Array (t_Array u8 (sz 504)) v_K =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize output
            (sz 0)
            (tmp.[ sz 0 ] <: t_Array u8 (sz 504))
        in
        let output:t_Array (t_Array u8 (sz 504)) v_K =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize output
            (sz 1)
            (tmp.[ sz 1 ] <: t_Array u8 (sz 504))
        in
        output, (XofState_X2 st <: t_XofState) <: (t_Array (t_Array u8 (sz 504)) v_K & t_XofState)
      | _ ->
        Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

            <:
            Rust_primitives.Hax.t_Never))
  | 3uy ->
    (match xof_state with
      | XofState_X3 st ->
        let tmp0, out:(Libcrux.Digest.t_Shake128StateX3 & t_Array (t_Array u8 (sz 504)) (sz 3)) =
          Libcrux.Digest.shake128_squeeze_nblocks_x3 (sz 504) st
        in
        let st:Libcrux.Digest.t_Shake128StateX3 = tmp0 in
        let tmp:t_Array (t_Array u8 (sz 504)) (sz 3) = out in
        let output:t_Array (t_Array u8 (sz 504)) v_K =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize output
            (sz 0)
            (tmp.[ sz 0 ] <: t_Array u8 (sz 504))
        in
        let output:t_Array (t_Array u8 (sz 504)) v_K =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize output
            (sz 1)
            (tmp.[ sz 1 ] <: t_Array u8 (sz 504))
        in
        let output:t_Array (t_Array u8 (sz 504)) v_K =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize output
            (sz 2)
            (tmp.[ sz 2 ] <: t_Array u8 (sz 504))
        in
        output, (XofState_X3 st <: t_XofState) <: (t_Array (t_Array u8 (sz 504)) v_K & t_XofState)
      | _ ->
        Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

            <:
            Rust_primitives.Hax.t_Never))
  | 4uy ->
    (match xof_state with
      | XofState_X4 st ->
        let tmp0, out:(Libcrux.Digest.t_Shake128StateX4 & t_Array (t_Array u8 (sz 504)) (sz 4)) =
          Libcrux.Digest.shake128_squeeze_nblocks_x4 (sz 504) st
        in
        let st:Libcrux.Digest.t_Shake128StateX4 = tmp0 in
        let tmp:t_Array (t_Array u8 (sz 504)) (sz 4) = out in
        let output:t_Array (t_Array u8 (sz 504)) v_K =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize output
            (sz 0)
            (tmp.[ sz 0 ] <: t_Array u8 (sz 504))
        in
        let output:t_Array (t_Array u8 (sz 504)) v_K =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize output
            (sz 1)
            (tmp.[ sz 1 ] <: t_Array u8 (sz 504))
        in
        let output:t_Array (t_Array u8 (sz 504)) v_K =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize output
            (sz 2)
            (tmp.[ sz 2 ] <: t_Array u8 (sz 504))
        in
        let output:t_Array (t_Array u8 (sz 504)) v_K =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize output
            (sz 3)
            (tmp.[ sz 3 ] <: t_Array u8 (sz 504))
        in
        output, (XofState_X4 st <: t_XofState) <: (t_Array (t_Array u8 (sz 504)) v_K & t_XofState)
      | _ ->
        Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

            <:
            Rust_primitives.Hax.t_Never))
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)
