module Libcrux_ml_kem.Hash_functions.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// The state.
/// It's only used for SHAKE128.
/// All other functions don't actually use any members.
type t_PortableHash (v_K: usize) = {
  f_shake128_state:t_Array Libcrux_sha3.Portable.t_KeccakState v_K
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (v_K: usize) : Libcrux_ml_kem.Hash_functions.t_Hash #(t_PortableHash v_K) v_K =
  {
    f_G_pre = (fun (input: t_Slice u8) -> true);
    f_G_post = (fun (input: t_Slice u8) (out: t_Array u8 (sz 64)) -> true);
    f_G
    =
    (fun (input: t_Slice u8) ->
        let digest:t_Array u8 (sz 64) = Rust_primitives.Hax.repeat 0uy (sz 64) in
        let digest:t_Array u8 (sz 64) = Libcrux_sha3.Portable.sha512 digest input in
        digest);
    f_H_pre = (fun (input: t_Slice u8) -> true);
    f_H_post = (fun (input: t_Slice u8) (out: t_Array u8 (sz 32)) -> true);
    f_H
    =
    (fun (input: t_Slice u8) ->
        let digest:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
        let digest:t_Array u8 (sz 32) = Libcrux_sha3.Portable.sha256 digest input in
        digest);
    f_PRF_pre = (fun (v_LEN: usize) (input: t_Slice u8) -> true);
    f_PRF_post = (fun (v_LEN: usize) (input: t_Slice u8) (out: t_Array u8 v_LEN) -> true);
    f_PRF
    =
    (fun (v_LEN: usize) (input: t_Slice u8) ->
        let digest:t_Array u8 v_LEN = Rust_primitives.Hax.repeat 0uy v_LEN in
        let digest:t_Array u8 v_LEN = Libcrux_sha3.Portable.shake256 digest input in
        digest);
    f_PRFxN_pre = (fun (v_LEN: usize) (input: t_Array (t_Array u8 (sz 33)) v_K) -> true);
    f_PRFxN_post
    =
    (fun
        (v_LEN: usize)
        (input: t_Array (t_Array u8 (sz 33)) v_K)
        (out1: t_Array (t_Array u8 v_LEN) v_K)
        ->
        true);
    f_PRFxN
    =
    (fun (v_LEN: usize) (input: t_Array (t_Array u8 (sz 33)) v_K) ->
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
        let out:t_Array (t_Array u8 v_LEN) v_K =
          Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat 0uy v_LEN <: t_Array u8 v_LEN) v_K
        in
        let out:t_Array (t_Array u8 v_LEN) v_K =
          Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
                  usize)
                ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = v_K }
                  <:
                  Core.Ops.Range.t_Range usize)
              <:
              Core.Ops.Range.t_Range usize)
            out
            (fun out i ->
                let out:t_Array (t_Array u8 v_LEN) v_K = out in
                let i:usize = i in
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
                  i
                  (Libcrux_sha3.Portable.shake256 (out.[ i ] <: t_Array u8 v_LEN)
                      (Rust_primitives.unsize (input.[ i ] <: t_Array u8 (sz 33)) <: t_Slice u8)
                    <:
                    t_Array u8 v_LEN)
                <:
                t_Array (t_Array u8 v_LEN) v_K)
        in
        out);
    f_shake128_init_absorb_pre = (fun (input: t_Array (t_Array u8 (sz 34)) v_K) -> true);
    f_shake128_init_absorb_post
    =
    (fun (input: t_Array (t_Array u8 (sz 34)) v_K) (out: t_PortableHash v_K) -> true);
    f_shake128_init_absorb
    =
    (fun (input: t_Array (t_Array u8 (sz 34)) v_K) ->
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
        let state:t_Array Libcrux_sha3.Portable.t_KeccakState v_K =
          Rust_primitives.Hax.repeat (Libcrux_sha3.Portable.Incremental.shake128_init ()
              <:
              Libcrux_sha3.Portable.t_KeccakState)
            v_K
        in
        let state:t_Array Libcrux_sha3.Portable.t_KeccakState v_K =
          Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
                  usize)
                ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = v_K }
                  <:
                  Core.Ops.Range.t_Range usize)
              <:
              Core.Ops.Range.t_Range usize)
            state
            (fun state i ->
                let state:t_Array Libcrux_sha3.Portable.t_KeccakState v_K = state in
                let i:usize = i in
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize state
                  i
                  (Libcrux_sha3.Portable.Incremental.shake128_absorb_final (state.[ i ]
                        <:
                        Libcrux_sha3.Portable.t_KeccakState)
                      (Rust_primitives.unsize (input.[ i ] <: t_Array u8 (sz 34)) <: t_Slice u8)
                    <:
                    Libcrux_sha3.Portable.t_KeccakState)
                <:
                t_Array Libcrux_sha3.Portable.t_KeccakState v_K)
        in
        { f_shake128_state = state } <: t_PortableHash v_K);
    f_shake128_squeeze_three_blocks_pre = (fun (self: t_PortableHash v_K) -> true);
    f_shake128_squeeze_three_blocks_post
    =
    (fun
        (self: t_PortableHash v_K)
        (out1: (t_PortableHash v_K & t_Array (t_Array u8 (sz 504)) v_K))
        ->
        true);
    f_shake128_squeeze_three_blocks
    =
    (fun (self: t_PortableHash v_K) ->
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
        let out:t_Array (t_Array u8 (sz 504)) v_K =
          Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat 0uy (sz 504) <: t_Array u8 (sz 504)
            )
            v_K
        in
        let out, self:(t_Array (t_Array u8 (sz 504)) v_K & t_PortableHash v_K) =
          Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
                  usize)
                ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = v_K }
                  <:
                  Core.Ops.Range.t_Range usize)
              <:
              Core.Ops.Range.t_Range usize)
            (out, self <: (t_Array (t_Array u8 (sz 504)) v_K & t_PortableHash v_K))
            (fun temp_0_ i ->
                let out, self:(t_Array (t_Array u8 (sz 504)) v_K & t_PortableHash v_K) = temp_0_ in
                let i:usize = i in
                let tmp0, tmp1:(Libcrux_sha3.Portable.t_KeccakState & t_Array u8 (sz 504)) =
                  Libcrux_sha3.Portable.Incremental.shake128_squeeze_first_three_blocks (self
                        .f_shake128_state.[ i ]
                      <:
                      Libcrux_sha3.Portable.t_KeccakState)
                    (out.[ i ] <: t_Array u8 (sz 504))
                in
                let self:t_PortableHash v_K =
                  {
                    self with
                    f_shake128_state
                    =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self
                        .f_shake128_state
                      i
                      tmp0
                  }
                  <:
                  t_PortableHash v_K
                in
                let out:t_Array (t_Array u8 (sz 504)) v_K =
                  Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out i tmp1
                in
                out, self <: (t_Array (t_Array u8 (sz 504)) v_K & t_PortableHash v_K))
        in
        let hax_temp_output:t_Array (t_Array u8 (sz 504)) v_K = out in
        self, hax_temp_output <: (t_PortableHash v_K & t_Array (t_Array u8 (sz 504)) v_K));
    f_shake128_squeeze_block_pre = (fun (self: t_PortableHash v_K) -> true);
    f_shake128_squeeze_block_post
    =
    (fun
        (self: t_PortableHash v_K)
        (out1: (t_PortableHash v_K & t_Array (t_Array u8 (sz 168)) v_K))
        ->
        true);
    f_shake128_squeeze_block
    =
    fun (self: t_PortableHash v_K) ->
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
      let out:t_Array (t_Array u8 (sz 168)) v_K =
        Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat 0uy (sz 168) <: t_Array u8 (sz 168))
          v_K
      in
      let out, self:(t_Array (t_Array u8 (sz 168)) v_K & t_PortableHash v_K) =
        Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
                usize)
              ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = v_K }
                <:
                Core.Ops.Range.t_Range usize)
            <:
            Core.Ops.Range.t_Range usize)
          (out, self <: (t_Array (t_Array u8 (sz 168)) v_K & t_PortableHash v_K))
          (fun temp_0_ i ->
              let out, self:(t_Array (t_Array u8 (sz 168)) v_K & t_PortableHash v_K) = temp_0_ in
              let i:usize = i in
              let tmp0, tmp1:(Libcrux_sha3.Portable.t_KeccakState & t_Array u8 (sz 168)) =
                Libcrux_sha3.Portable.Incremental.shake128_squeeze_next_block (self.f_shake128_state.[
                      i ]
                    <:
                    Libcrux_sha3.Portable.t_KeccakState)
                  (out.[ i ] <: t_Array u8 (sz 168))
              in
              let self:t_PortableHash v_K =
                {
                  self with
                  f_shake128_state
                  =
                  Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_shake128_state
                    i
                    tmp0
                }
                <:
                t_PortableHash v_K
              in
              let out:t_Array (t_Array u8 (sz 168)) v_K =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out i tmp1
              in
              out, self <: (t_Array (t_Array u8 (sz 168)) v_K & t_PortableHash v_K))
      in
      let hax_temp_output:t_Array (t_Array u8 (sz 168)) v_K = out in
      self, hax_temp_output <: (t_PortableHash v_K & t_Array (t_Array u8 (sz 168)) v_K)
  }
