module Libcrux_ml_kem.Hash_functions.Neon
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// The state.
/// It's only used for SHAKE128.
/// All other functions don't actually use any members.
type t_Simd128Hash = {
  f_shake128_state:t_Array Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2 (sz 2)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (v_K: usize) : Libcrux_ml_kem.Hash_functions.t_Hash t_Simd128Hash v_K =
  {
    f_G_pre = (fun (input: t_Slice u8) -> true);
    f_G_post = (fun (input: t_Slice u8) (out: t_Array u8 (sz 64)) -> true);
    f_G
    =
    (fun (input: t_Slice u8) ->
        let digest:t_Array u8 (sz 64) = Rust_primitives.Hax.repeat 0uy (sz 64) in
        let digest:t_Array u8 (sz 64) = Libcrux_sha3.Neon.sha512 digest input in
        digest);
    f_H_pre = (fun (input: t_Slice u8) -> true);
    f_H_post = (fun (input: t_Slice u8) (out: t_Array u8 (sz 32)) -> true);
    f_H
    =
    (fun (input: t_Slice u8) ->
        let digest:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
        let digest:t_Array u8 (sz 32) = Libcrux_sha3.Neon.sha256 digest input in
        digest);
    f_PRF_pre = (fun (v_LEN: usize) (input: t_Slice u8) -> true);
    f_PRF_post = (fun (v_LEN: usize) (input: t_Slice u8) (out: t_Array u8 v_LEN) -> true);
    f_PRF
    =
    (fun (v_LEN: usize) (input: t_Slice u8) ->
        let digest:t_Array u8 v_LEN = Rust_primitives.Hax.repeat 0uy v_LEN in
        let dummy:t_Array u8 v_LEN = Rust_primitives.Hax.repeat 0uy v_LEN in
        let tmp0, tmp1:(t_Array u8 v_LEN & t_Array u8 v_LEN) =
          Libcrux_sha3.Neon.X2.shake256 input input digest dummy
        in
        let digest:t_Array u8 v_LEN = tmp0 in
        let dummy:t_Array u8 v_LEN = tmp1 in
        let _:Prims.unit = () in
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
            let tmp0, tmp1:(t_Array u8 v_LEN & t_Array u8 v_LEN) =
              Libcrux_sha3.Neon.X2.shake256 (Rust_primitives.unsize (input.[ sz 0 ]
                      <:
                      t_Array u8 (sz 33))
                  <:
                  t_Slice u8)
                (Rust_primitives.unsize (input.[ sz 1 ] <: t_Array u8 (sz 33)) <: t_Slice u8)
                out0
                out1
            in
            let out0:t_Array u8 v_LEN = tmp0 in
            let out1:t_Array u8 v_LEN = tmp1 in
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
            let tmp0, tmp1:(t_Array u8 v_LEN & t_Array u8 v_LEN) =
              Libcrux_sha3.Neon.X2.shake256 (Rust_primitives.unsize (input.[ sz 0 ]
                      <:
                      t_Array u8 (sz 33))
                  <:
                  t_Slice u8)
                (Rust_primitives.unsize (input.[ sz 1 ] <: t_Array u8 (sz 33)) <: t_Slice u8)
                out0
                out1
            in
            let out0:t_Array u8 v_LEN = tmp0 in
            let out1:t_Array u8 v_LEN = tmp1 in
            let _:Prims.unit = () in
            let tmp0, tmp1:(t_Array u8 v_LEN & t_Array u8 v_LEN) =
              Libcrux_sha3.Neon.X2.shake256 (Rust_primitives.unsize (input.[ sz 2 ]
                      <:
                      t_Array u8 (sz 33))
                  <:
                  t_Slice u8)
                (Rust_primitives.unsize (input.[ sz 2 ] <: t_Array u8 (sz 33)) <: t_Slice u8)
                out2
                out3
            in
            let out2:t_Array u8 v_LEN = tmp0 in
            let out3:t_Array u8 v_LEN = tmp1 in
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
            let tmp0, tmp1:(t_Array u8 v_LEN & t_Array u8 v_LEN) =
              Libcrux_sha3.Neon.X2.shake256 (Rust_primitives.unsize (input.[ sz 0 ]
                      <:
                      t_Array u8 (sz 33))
                  <:
                  t_Slice u8)
                (Rust_primitives.unsize (input.[ sz 1 ] <: t_Array u8 (sz 33)) <: t_Slice u8)
                out0
                out1
            in
            let out0:t_Array u8 v_LEN = tmp0 in
            let out1:t_Array u8 v_LEN = tmp1 in
            let _:Prims.unit = () in
            let tmp0, tmp1:(t_Array u8 v_LEN & t_Array u8 v_LEN) =
              Libcrux_sha3.Neon.X2.shake256 (Rust_primitives.unsize (input.[ sz 2 ]
                      <:
                      t_Array u8 (sz 33))
                  <:
                  t_Slice u8)
                (Rust_primitives.unsize (input.[ sz 3 ] <: t_Array u8 (sz 33)) <: t_Slice u8)
                out2
                out3
            in
            let out2:t_Array u8 v_LEN = tmp0 in
            let out3:t_Array u8 v_LEN = tmp1 in
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
    (fun (input: t_Array (t_Array u8 (sz 34)) v_K) (out: t_Simd128Hash) -> true);
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
        let state:t_Array Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2 (sz 2) =
          let list =
            [
              Libcrux_sha3.Neon.X2.Incremental.shake128_init ();
              Libcrux_sha3.Neon.X2.Incremental.shake128_init ()
            ]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
          Rust_primitives.Hax.array_of_list 2 list
        in
        let state:t_Array Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2 (sz 2) =
          match cast (v_K <: usize) <: u8 with
          | 2uy ->
            let state:t_Array Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2 (sz 2) =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize state
                (sz 0)
                (Libcrux_sha3.Neon.X2.Incremental.shake128_absorb_final (state.[ sz 0 ]
                      <:
                      Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2)
                    (Rust_primitives.unsize (input.[ sz 0 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
                    (Rust_primitives.unsize (input.[ sz 1 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
                  <:
                  Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2)
            in
            state
          | 3uy ->
            let state:t_Array Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2 (sz 2) =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize state
                (sz 0)
                (Libcrux_sha3.Neon.X2.Incremental.shake128_absorb_final (state.[ sz 0 ]
                      <:
                      Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2)
                    (Rust_primitives.unsize (input.[ sz 0 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
                    (Rust_primitives.unsize (input.[ sz 1 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
                  <:
                  Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2)
            in
            let state:t_Array Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2 (sz 2) =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize state
                (sz 1)
                (Libcrux_sha3.Neon.X2.Incremental.shake128_absorb_final (state.[ sz 1 ]
                      <:
                      Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2)
                    (Rust_primitives.unsize (input.[ sz 2 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
                    (Rust_primitives.unsize (input.[ sz 2 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
                  <:
                  Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2)
            in
            state
          | 4uy ->
            let state:t_Array Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2 (sz 2) =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize state
                (sz 0)
                (Libcrux_sha3.Neon.X2.Incremental.shake128_absorb_final (state.[ sz 0 ]
                      <:
                      Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2)
                    (Rust_primitives.unsize (input.[ sz 0 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
                    (Rust_primitives.unsize (input.[ sz 1 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
                  <:
                  Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2)
            in
            let state:t_Array Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2 (sz 2) =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize state
                (sz 1)
                (Libcrux_sha3.Neon.X2.Incremental.shake128_absorb_final (state.[ sz 1 ]
                      <:
                      Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2)
                    (Rust_primitives.unsize (input.[ sz 2 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
                    (Rust_primitives.unsize (input.[ sz 3 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
                  <:
                  Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2)
            in
            state
          | _ -> state
        in
        { f_shake128_state = state } <: t_Simd128Hash);
    f_shake128_squeeze_three_blocks_pre = (fun (self: t_Simd128Hash) -> true);
    f_shake128_squeeze_three_blocks_post
    =
    (fun (self: t_Simd128Hash) (out4: (t_Simd128Hash & t_Array (t_Array u8 (sz 504)) v_K)) -> true);
    f_shake128_squeeze_three_blocks
    =
    (fun (self: t_Simd128Hash) ->
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
        let out, out0, out1, out2, out3, self:(t_Array (t_Array u8 (sz 504)) v_K &
          t_Array u8 (sz 504) &
          t_Array u8 (sz 504) &
          t_Array u8 (sz 504) &
          t_Array u8 (sz 504) &
          t_Simd128Hash) =
          match cast (v_K <: usize) <: u8 with
          | 2uy ->
            let tmp0, tmp1, tmp2:(Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2 &
              t_Array u8 (sz 504) &
              t_Array u8 (sz 504)) =
              Libcrux_sha3.Neon.X2.Incremental.shake128_squeeze_first_three_blocks (self
                    .f_shake128_state.[ sz 0 ]
                  <:
                  Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2)
                out0
                out1
            in
            let self:t_Simd128Hash =
              {
                self with
                f_shake128_state
                =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_shake128_state
                  (sz 0)
                  tmp0
              }
              <:
              t_Simd128Hash
            in
            let out0:t_Array u8 (sz 504) = tmp1 in
            let out1:t_Array u8 (sz 504) = tmp2 in
            let _:Prims.unit = () in
            let out:t_Array (t_Array u8 (sz 504)) v_K =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 0) out0
            in
            let out:t_Array (t_Array u8 (sz 504)) v_K =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 1) out1
            in
            out, out0, out1, out2, out3, self
            <:
            (t_Array (t_Array u8 (sz 504)) v_K & t_Array u8 (sz 504) & t_Array u8 (sz 504) &
              t_Array u8 (sz 504) &
              t_Array u8 (sz 504) &
              t_Simd128Hash)
          | 3uy ->
            let tmp0, tmp1, tmp2:(Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2 &
              t_Array u8 (sz 504) &
              t_Array u8 (sz 504)) =
              Libcrux_sha3.Neon.X2.Incremental.shake128_squeeze_first_three_blocks (self
                    .f_shake128_state.[ sz 0 ]
                  <:
                  Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2)
                out0
                out1
            in
            let self:t_Simd128Hash =
              {
                self with
                f_shake128_state
                =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_shake128_state
                  (sz 0)
                  tmp0
              }
              <:
              t_Simd128Hash
            in
            let out0:t_Array u8 (sz 504) = tmp1 in
            let out1:t_Array u8 (sz 504) = tmp2 in
            let _:Prims.unit = () in
            let tmp0, tmp1, tmp2:(Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2 &
              t_Array u8 (sz 504) &
              t_Array u8 (sz 504)) =
              Libcrux_sha3.Neon.X2.Incremental.shake128_squeeze_first_three_blocks (self
                    .f_shake128_state.[ sz 1 ]
                  <:
                  Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2)
                out2
                out3
            in
            let self:t_Simd128Hash =
              {
                self with
                f_shake128_state
                =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_shake128_state
                  (sz 1)
                  tmp0
              }
              <:
              t_Simd128Hash
            in
            let out2:t_Array u8 (sz 504) = tmp1 in
            let out3:t_Array u8 (sz 504) = tmp2 in
            let _:Prims.unit = () in
            let out:t_Array (t_Array u8 (sz 504)) v_K =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 0) out0
            in
            let out:t_Array (t_Array u8 (sz 504)) v_K =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 1) out1
            in
            let out:t_Array (t_Array u8 (sz 504)) v_K =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 2) out2
            in
            out, out0, out1, out2, out3, self
            <:
            (t_Array (t_Array u8 (sz 504)) v_K & t_Array u8 (sz 504) & t_Array u8 (sz 504) &
              t_Array u8 (sz 504) &
              t_Array u8 (sz 504) &
              t_Simd128Hash)
          | 4uy ->
            let tmp0, tmp1, tmp2:(Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2 &
              t_Array u8 (sz 504) &
              t_Array u8 (sz 504)) =
              Libcrux_sha3.Neon.X2.Incremental.shake128_squeeze_first_three_blocks (self
                    .f_shake128_state.[ sz 0 ]
                  <:
                  Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2)
                out0
                out1
            in
            let self:t_Simd128Hash =
              {
                self with
                f_shake128_state
                =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_shake128_state
                  (sz 0)
                  tmp0
              }
              <:
              t_Simd128Hash
            in
            let out0:t_Array u8 (sz 504) = tmp1 in
            let out1:t_Array u8 (sz 504) = tmp2 in
            let _:Prims.unit = () in
            let tmp0, tmp1, tmp2:(Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2 &
              t_Array u8 (sz 504) &
              t_Array u8 (sz 504)) =
              Libcrux_sha3.Neon.X2.Incremental.shake128_squeeze_first_three_blocks (self
                    .f_shake128_state.[ sz 1 ]
                  <:
                  Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2)
                out2
                out3
            in
            let self:t_Simd128Hash =
              {
                self with
                f_shake128_state
                =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_shake128_state
                  (sz 1)
                  tmp0
              }
              <:
              t_Simd128Hash
            in
            let out2:t_Array u8 (sz 504) = tmp1 in
            let out3:t_Array u8 (sz 504) = tmp2 in
            let _:Prims.unit = () in
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
            out, out0, out1, out2, out3, self
            <:
            (t_Array (t_Array u8 (sz 504)) v_K & t_Array u8 (sz 504) & t_Array u8 (sz 504) &
              t_Array u8 (sz 504) &
              t_Array u8 (sz 504) &
              t_Simd128Hash)
          | _ ->
            out, out0, out1, out2, out3, self
            <:
            (t_Array (t_Array u8 (sz 504)) v_K & t_Array u8 (sz 504) & t_Array u8 (sz 504) &
              t_Array u8 (sz 504) &
              t_Array u8 (sz 504) &
              t_Simd128Hash)
        in
        let hax_temp_output:t_Array (t_Array u8 (sz 504)) v_K = out in
        self, hax_temp_output <: (t_Simd128Hash & t_Array (t_Array u8 (sz 504)) v_K));
    f_shake128_squeeze_block_pre = (fun (self: t_Simd128Hash) -> true);
    f_shake128_squeeze_block_post
    =
    (fun (self: t_Simd128Hash) (out4: (t_Simd128Hash & t_Array (t_Array u8 (sz 168)) v_K)) -> true);
    f_shake128_squeeze_block
    =
    fun (self: t_Simd128Hash) ->
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
      let out, out0, out1, out2, out3, self:(t_Array (t_Array u8 (sz 168)) v_K & t_Array u8 (sz 168) &
        t_Array u8 (sz 168) &
        t_Array u8 (sz 168) &
        t_Array u8 (sz 168) &
        t_Simd128Hash) =
        match cast (v_K <: usize) <: u8 with
        | 2uy ->
          let tmp0, tmp1, tmp2:(Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2 &
            t_Array u8 (sz 168) &
            t_Array u8 (sz 168)) =
            Libcrux_sha3.Neon.X2.Incremental.shake128_squeeze_next_block (self.f_shake128_state.[ sz
                  0 ]
                <:
                Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2)
              out0
              out1
          in
          let self:t_Simd128Hash =
            {
              self with
              f_shake128_state
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_shake128_state
                (sz 0)
                tmp0
            }
            <:
            t_Simd128Hash
          in
          let out0:t_Array u8 (sz 168) = tmp1 in
          let out1:t_Array u8 (sz 168) = tmp2 in
          let _:Prims.unit = () in
          let out:t_Array (t_Array u8 (sz 168)) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 0) out0
          in
          let out:t_Array (t_Array u8 (sz 168)) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 1) out1
          in
          out, out0, out1, out2, out3, self
          <:
          (t_Array (t_Array u8 (sz 168)) v_K & t_Array u8 (sz 168) & t_Array u8 (sz 168) &
            t_Array u8 (sz 168) &
            t_Array u8 (sz 168) &
            t_Simd128Hash)
        | 3uy ->
          let tmp0, tmp1, tmp2:(Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2 &
            t_Array u8 (sz 168) &
            t_Array u8 (sz 168)) =
            Libcrux_sha3.Neon.X2.Incremental.shake128_squeeze_next_block (self.f_shake128_state.[ sz
                  0 ]
                <:
                Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2)
              out0
              out1
          in
          let self:t_Simd128Hash =
            {
              self with
              f_shake128_state
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_shake128_state
                (sz 0)
                tmp0
            }
            <:
            t_Simd128Hash
          in
          let out0:t_Array u8 (sz 168) = tmp1 in
          let out1:t_Array u8 (sz 168) = tmp2 in
          let _:Prims.unit = () in
          let tmp0, tmp1, tmp2:(Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2 &
            t_Array u8 (sz 168) &
            t_Array u8 (sz 168)) =
            Libcrux_sha3.Neon.X2.Incremental.shake128_squeeze_next_block (self.f_shake128_state.[ sz
                  1 ]
                <:
                Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2)
              out2
              out3
          in
          let self:t_Simd128Hash =
            {
              self with
              f_shake128_state
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_shake128_state
                (sz 1)
                tmp0
            }
            <:
            t_Simd128Hash
          in
          let out2:t_Array u8 (sz 168) = tmp1 in
          let out3:t_Array u8 (sz 168) = tmp2 in
          let _:Prims.unit = () in
          let out:t_Array (t_Array u8 (sz 168)) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 0) out0
          in
          let out:t_Array (t_Array u8 (sz 168)) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 1) out1
          in
          let out:t_Array (t_Array u8 (sz 168)) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 2) out2
          in
          out, out0, out1, out2, out3, self
          <:
          (t_Array (t_Array u8 (sz 168)) v_K & t_Array u8 (sz 168) & t_Array u8 (sz 168) &
            t_Array u8 (sz 168) &
            t_Array u8 (sz 168) &
            t_Simd128Hash)
        | 4uy ->
          let tmp0, tmp1, tmp2:(Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2 &
            t_Array u8 (sz 168) &
            t_Array u8 (sz 168)) =
            Libcrux_sha3.Neon.X2.Incremental.shake128_squeeze_next_block (self.f_shake128_state.[ sz
                  0 ]
                <:
                Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2)
              out0
              out1
          in
          let self:t_Simd128Hash =
            {
              self with
              f_shake128_state
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_shake128_state
                (sz 0)
                tmp0
            }
            <:
            t_Simd128Hash
          in
          let out0:t_Array u8 (sz 168) = tmp1 in
          let out1:t_Array u8 (sz 168) = tmp2 in
          let _:Prims.unit = () in
          let tmp0, tmp1, tmp2:(Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2 &
            t_Array u8 (sz 168) &
            t_Array u8 (sz 168)) =
            Libcrux_sha3.Neon.X2.Incremental.shake128_squeeze_next_block (self.f_shake128_state.[ sz
                  1 ]
                <:
                Libcrux_sha3.Neon.X2.Incremental.t_KeccakState2)
              out2
              out3
          in
          let self:t_Simd128Hash =
            {
              self with
              f_shake128_state
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_shake128_state
                (sz 1)
                tmp0
            }
            <:
            t_Simd128Hash
          in
          let out2:t_Array u8 (sz 168) = tmp1 in
          let out3:t_Array u8 (sz 168) = tmp2 in
          let _:Prims.unit = () in
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
          out, out0, out1, out2, out3, self
          <:
          (t_Array (t_Array u8 (sz 168)) v_K & t_Array u8 (sz 168) & t_Array u8 (sz 168) &
            t_Array u8 (sz 168) &
            t_Array u8 (sz 168) &
            t_Simd128Hash)
        | _ ->
          out, out0, out1, out2, out3, self
          <:
          (t_Array (t_Array u8 (sz 168)) v_K & t_Array u8 (sz 168) & t_Array u8 (sz 168) &
            t_Array u8 (sz 168) &
            t_Array u8 (sz 168) &
            t_Simd128Hash)
      in
      let hax_temp_output:t_Array (t_Array u8 (sz 168)) v_K = out in
      self, hax_temp_output <: (t_Simd128Hash & t_Array (t_Array u8 (sz 168)) v_K)
  }
