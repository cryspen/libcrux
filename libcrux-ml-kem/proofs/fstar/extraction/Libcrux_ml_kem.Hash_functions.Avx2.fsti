module Libcrux_ml_kem.Hash_functions.Avx2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// The state.
/// It's only used for SHAKE128.
/// All other functions don't actually use any members.
type t_Simd256Hash = { f_shake128_state:Libcrux_sha3.Avx2.X4.Incremental.t_KeccakState4 }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (v_K: usize) : Libcrux_ml_kem.Hash_functions.t_Hash t_Simd256Hash v_K =
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
        (out4: t_Array (t_Array u8 v_LEN) v_K)
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
        let out0:t_Array u8 v_LEN = Rust_primitives.Hax.repeat 0uy v_LEN in
        let out1:t_Array u8 v_LEN = Rust_primitives.Hax.repeat 0uy v_LEN in
        let out2:t_Array u8 v_LEN = Rust_primitives.Hax.repeat 0uy v_LEN in
        let out3:t_Array u8 v_LEN = Rust_primitives.Hax.repeat 0uy v_LEN in
        let out, out0, out1, out2, out3:(t_Array (t_Array u8 v_LEN) v_K & t_Array u8 v_LEN &
          t_Array u8 v_LEN &
          t_Array u8 v_LEN &
          t_Array u8 v_LEN) =
          match cast (v_K <: usize) <: u8 with
          | 2uy ->
            let tmp0, tmp1, tmp2, tmp3:(t_Array u8 v_LEN & t_Array u8 v_LEN & t_Array u8 v_LEN &
              t_Array u8 v_LEN) =
              Libcrux_sha3.Avx2.X4.shake256 (Rust_primitives.unsize (input.[ sz 0 ]
                      <:
                      t_Array u8 (sz 33))
                  <:
                  t_Slice u8)
                (Rust_primitives.unsize (input.[ sz 1 ] <: t_Array u8 (sz 33)) <: t_Slice u8)
                (Rust_primitives.unsize (input.[ sz 0 ] <: t_Array u8 (sz 33)) <: t_Slice u8)
                (Rust_primitives.unsize (input.[ sz 0 ] <: t_Array u8 (sz 33)) <: t_Slice u8)
                out0
                out1
                out2
                out3
            in
            let out0:t_Array u8 v_LEN = tmp0 in
            let out1:t_Array u8 v_LEN = tmp1 in
            let out2:t_Array u8 v_LEN = tmp2 in
            let out3:t_Array u8 v_LEN = tmp3 in
            let _:Prims.unit = () in
            let out:t_Array (t_Array u8 v_LEN) v_K =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 0) out0
            in
            let out:t_Array (t_Array u8 v_LEN) v_K =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 1) out1
            in
            out, out0, out1, out2, out3
            <:
            (t_Array (t_Array u8 v_LEN) v_K & t_Array u8 v_LEN & t_Array u8 v_LEN & t_Array u8 v_LEN &
              t_Array u8 v_LEN)
          | 3uy ->
            let tmp0, tmp1, tmp2, tmp3:(t_Array u8 v_LEN & t_Array u8 v_LEN & t_Array u8 v_LEN &
              t_Array u8 v_LEN) =
              Libcrux_sha3.Avx2.X4.shake256 (Rust_primitives.unsize (input.[ sz 0 ]
                      <:
                      t_Array u8 (sz 33))
                  <:
                  t_Slice u8)
                (Rust_primitives.unsize (input.[ sz 1 ] <: t_Array u8 (sz 33)) <: t_Slice u8)
                (Rust_primitives.unsize (input.[ sz 2 ] <: t_Array u8 (sz 33)) <: t_Slice u8)
                (Rust_primitives.unsize (input.[ sz 0 ] <: t_Array u8 (sz 33)) <: t_Slice u8)
                out0
                out1
                out2
                out3
            in
            let out0:t_Array u8 v_LEN = tmp0 in
            let out1:t_Array u8 v_LEN = tmp1 in
            let out2:t_Array u8 v_LEN = tmp2 in
            let out3:t_Array u8 v_LEN = tmp3 in
            let _:Prims.unit = () in
            let out:t_Array (t_Array u8 v_LEN) v_K =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 0) out0
            in
            let out:t_Array (t_Array u8 v_LEN) v_K =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 1) out1
            in
            let out:t_Array (t_Array u8 v_LEN) v_K =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 2) out2
            in
            out, out0, out1, out2, out3
            <:
            (t_Array (t_Array u8 v_LEN) v_K & t_Array u8 v_LEN & t_Array u8 v_LEN & t_Array u8 v_LEN &
              t_Array u8 v_LEN)
          | 4uy ->
            let tmp0, tmp1, tmp2, tmp3:(t_Array u8 v_LEN & t_Array u8 v_LEN & t_Array u8 v_LEN &
              t_Array u8 v_LEN) =
              Libcrux_sha3.Avx2.X4.shake256 (Rust_primitives.unsize (input.[ sz 0 ]
                      <:
                      t_Array u8 (sz 33))
                  <:
                  t_Slice u8)
                (Rust_primitives.unsize (input.[ sz 1 ] <: t_Array u8 (sz 33)) <: t_Slice u8)
                (Rust_primitives.unsize (input.[ sz 2 ] <: t_Array u8 (sz 33)) <: t_Slice u8)
                (Rust_primitives.unsize (input.[ sz 3 ] <: t_Array u8 (sz 33)) <: t_Slice u8)
                out0
                out1
                out2
                out3
            in
            let out0:t_Array u8 v_LEN = tmp0 in
            let out1:t_Array u8 v_LEN = tmp1 in
            let out2:t_Array u8 v_LEN = tmp2 in
            let out3:t_Array u8 v_LEN = tmp3 in
            let _:Prims.unit = () in
            let out:t_Array (t_Array u8 v_LEN) v_K =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 0) out0
            in
            let out:t_Array (t_Array u8 v_LEN) v_K =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 1) out1
            in
            let out:t_Array (t_Array u8 v_LEN) v_K =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 2) out2
            in
            let out:t_Array (t_Array u8 v_LEN) v_K =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 3) out3
            in
            out, out0, out1, out2, out3
            <:
            (t_Array (t_Array u8 v_LEN) v_K & t_Array u8 v_LEN & t_Array u8 v_LEN & t_Array u8 v_LEN &
              t_Array u8 v_LEN)
          | _ ->
            out, out0, out1, out2, out3
            <:
            (t_Array (t_Array u8 v_LEN) v_K & t_Array u8 v_LEN & t_Array u8 v_LEN & t_Array u8 v_LEN &
              t_Array u8 v_LEN)
        in
        out);
    f_shake128_init_absorb_pre = (fun (input: t_Array (t_Array u8 (sz 34)) v_K) -> true);
    f_shake128_init_absorb_post
    =
    (fun (input: t_Array (t_Array u8 (sz 34)) v_K) (out: t_Simd256Hash) -> true);
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
        let state:Libcrux_sha3.Avx2.X4.Incremental.t_KeccakState4 =
          Libcrux_sha3.Avx2.X4.Incremental.shake128_init ()
        in
        let state:Libcrux_sha3.Avx2.X4.Incremental.t_KeccakState4 =
          match cast (v_K <: usize) <: u8 with
          | 2uy ->
            let state:Libcrux_sha3.Avx2.X4.Incremental.t_KeccakState4 =
              Libcrux_sha3.Avx2.X4.Incremental.shake128_absorb_final state
                (Rust_primitives.unsize (input.[ sz 0 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
                (Rust_primitives.unsize (input.[ sz 1 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
                (Rust_primitives.unsize (input.[ sz 0 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
                (Rust_primitives.unsize (input.[ sz 0 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
            in
            state
          | 3uy ->
            let state:Libcrux_sha3.Avx2.X4.Incremental.t_KeccakState4 =
              Libcrux_sha3.Avx2.X4.Incremental.shake128_absorb_final state
                (Rust_primitives.unsize (input.[ sz 0 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
                (Rust_primitives.unsize (input.[ sz 1 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
                (Rust_primitives.unsize (input.[ sz 2 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
                (Rust_primitives.unsize (input.[ sz 0 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
            in
            state
          | 4uy ->
            let state:Libcrux_sha3.Avx2.X4.Incremental.t_KeccakState4 =
              Libcrux_sha3.Avx2.X4.Incremental.shake128_absorb_final state
                (Rust_primitives.unsize (input.[ sz 0 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
                (Rust_primitives.unsize (input.[ sz 1 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
                (Rust_primitives.unsize (input.[ sz 2 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
                (Rust_primitives.unsize (input.[ sz 3 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
            in
            state
          | _ -> state
        in
        { f_shake128_state = state } <: t_Simd256Hash);
    f_shake128_squeeze_three_blocks_pre = (fun (self: t_Simd256Hash) -> true);
    f_shake128_squeeze_three_blocks_post
    =
    (fun (self: t_Simd256Hash) (out4: (t_Simd256Hash & t_Array (t_Array u8 (sz 504)) v_K)) -> true);
    f_shake128_squeeze_three_blocks
    =
    (fun (self: t_Simd256Hash) ->
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
        let out0:t_Array u8 (sz 504) = Rust_primitives.Hax.repeat 0uy (sz 504) in
        let out1:t_Array u8 (sz 504) = Rust_primitives.Hax.repeat 0uy (sz 504) in
        let out2:t_Array u8 (sz 504) = Rust_primitives.Hax.repeat 0uy (sz 504) in
        let out3:t_Array u8 (sz 504) = Rust_primitives.Hax.repeat 0uy (sz 504) in
        let tmp0, tmp1, tmp2, tmp3, tmp4:(Libcrux_sha3.Avx2.X4.Incremental.t_KeccakState4 &
          t_Array u8 (sz 504) &
          t_Array u8 (sz 504) &
          t_Array u8 (sz 504) &
          t_Array u8 (sz 504)) =
          Libcrux_sha3.Avx2.X4.Incremental.shake128_squeeze_first_three_blocks self.f_shake128_state
            out0
            out1
            out2
            out3
        in
        let self:t_Simd256Hash = { self with f_shake128_state = tmp0 } <: t_Simd256Hash in
        let out0:t_Array u8 (sz 504) = tmp1 in
        let out1:t_Array u8 (sz 504) = tmp2 in
        let out2:t_Array u8 (sz 504) = tmp3 in
        let out3:t_Array u8 (sz 504) = tmp4 in
        let _:Prims.unit = () in
        let out:t_Array (t_Array u8 (sz 504)) v_K =
          match cast (v_K <: usize) <: u8 with
          | 2uy ->
            let out:t_Array (t_Array u8 (sz 504)) v_K =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 0) out0
            in
            let out:t_Array (t_Array u8 (sz 504)) v_K =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 1) out1
            in
            out
          | 3uy ->
            let out:t_Array (t_Array u8 (sz 504)) v_K =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 0) out0
            in
            let out:t_Array (t_Array u8 (sz 504)) v_K =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 1) out1
            in
            let out:t_Array (t_Array u8 (sz 504)) v_K =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 2) out2
            in
            out
          | 4uy ->
            let out:t_Array (t_Array u8 (sz 504)) v_K =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 0) out0
            in
            let out:t_Array (t_Array u8 (sz 504)) v_K =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 1) out1
            in
            let out:t_Array (t_Array u8 (sz 504)) v_K =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 2) out2
            in
            let out:t_Array (t_Array u8 (sz 504)) v_K =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 3) out3
            in
            out
          | _ -> out
        in
        let hax_temp_output:t_Array (t_Array u8 (sz 504)) v_K = out in
        self, hax_temp_output <: (t_Simd256Hash & t_Array (t_Array u8 (sz 504)) v_K));
    f_shake128_squeeze_block_pre = (fun (self: t_Simd256Hash) -> true);
    f_shake128_squeeze_block_post
    =
    (fun (self: t_Simd256Hash) (out4: (t_Simd256Hash & t_Array (t_Array u8 (sz 168)) v_K)) -> true);
    f_shake128_squeeze_block
    =
    fun (self: t_Simd256Hash) ->
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
      let out0:t_Array u8 (sz 168) = Rust_primitives.Hax.repeat 0uy (sz 168) in
      let out1:t_Array u8 (sz 168) = Rust_primitives.Hax.repeat 0uy (sz 168) in
      let out2:t_Array u8 (sz 168) = Rust_primitives.Hax.repeat 0uy (sz 168) in
      let out3:t_Array u8 (sz 168) = Rust_primitives.Hax.repeat 0uy (sz 168) in
      let tmp0, tmp1, tmp2, tmp3, tmp4:(Libcrux_sha3.Avx2.X4.Incremental.t_KeccakState4 &
        t_Array u8 (sz 168) &
        t_Array u8 (sz 168) &
        t_Array u8 (sz 168) &
        t_Array u8 (sz 168)) =
        Libcrux_sha3.Avx2.X4.Incremental.shake128_squeeze_next_block self.f_shake128_state
          out0
          out1
          out2
          out3
      in
      let self:t_Simd256Hash = { self with f_shake128_state = tmp0 } <: t_Simd256Hash in
      let out0:t_Array u8 (sz 168) = tmp1 in
      let out1:t_Array u8 (sz 168) = tmp2 in
      let out2:t_Array u8 (sz 168) = tmp3 in
      let out3:t_Array u8 (sz 168) = tmp4 in
      let _:Prims.unit = () in
      let out:t_Array (t_Array u8 (sz 168)) v_K =
        match cast (v_K <: usize) <: u8 with
        | 2uy ->
          let out:t_Array (t_Array u8 (sz 168)) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 0) out0
          in
          let out:t_Array (t_Array u8 (sz 168)) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 1) out1
          in
          out
        | 3uy ->
          let out:t_Array (t_Array u8 (sz 168)) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 0) out0
          in
          let out:t_Array (t_Array u8 (sz 168)) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 1) out1
          in
          let out:t_Array (t_Array u8 (sz 168)) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 2) out2
          in
          out
        | 4uy ->
          let out:t_Array (t_Array u8 (sz 168)) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 0) out0
          in
          let out:t_Array (t_Array u8 (sz 168)) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 1) out1
          in
          let out:t_Array (t_Array u8 (sz 168)) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 2) out2
          in
          let out:t_Array (t_Array u8 (sz 168)) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 3) out3
          in
          out
        | _ -> out
      in
      let hax_temp_output:t_Array (t_Array u8 (sz 168)) v_K = out in
      self, hax_temp_output <: (t_Simd256Hash & t_Array (t_Array u8 (sz 168)) v_K)
  }
