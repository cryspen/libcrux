module Libcrux.Kem.Kyber.Hash_functions
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_G (input: t_Slice u8) : t_Array u8 (sz 64) = Libcrux.Digest.sha3_512_ input

let v_H (input: t_Slice u8) : t_Array u8 (sz 32) = Libcrux.Digest.sha3_256_ input

let v_PRF (v_LEN: usize) (input: t_Slice u8) : t_Array u8 v_LEN =
  Libcrux.Digest.shake256 v_LEN input

let v_XOFx4 (v_K: usize) (input: t_Array (t_Array u8 (sz 34)) v_K)
    : t_Array (t_Array u8 (sz 840)) v_K =
  let out:t_Array (t_Array u8 (sz 840)) v_K =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat 0uy (sz 840) <: t_Array u8 (sz 840)) v_K
  in
  match cast (v_K <: usize) <: u8 with
  | 2uy ->
    let d0, d1, _, _:(t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
      t_Array u8 (sz 840)) =
      Libcrux.Hacl.Sha3.Simd256.shake128 (sz 840)
        (Rust_primitives.unsize (input.[ sz 0 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
        (Rust_primitives.unsize (input.[ sz 1 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
        (Rust_primitives.unsize (input.[ sz 0 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
        (Rust_primitives.unsize (input.[ sz 1 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
    in
    let out:t_Array (t_Array u8 (sz 840)) v_K =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 0) d0
    in
    let out:t_Array (t_Array u8 (sz 840)) v_K =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 1) d1
    in
    out
  | 3uy ->
    let d0, d1, d2, _:(t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
      t_Array u8 (sz 840)) =
      Libcrux.Hacl.Sha3.Simd256.shake128 (sz 840)
        (Rust_primitives.unsize (input.[ sz 0 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
        (Rust_primitives.unsize (input.[ sz 1 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
        (Rust_primitives.unsize (input.[ sz 2 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
        (Rust_primitives.unsize (input.[ sz 0 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
    in
    let out:t_Array (t_Array u8 (sz 840)) v_K =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 0) d0
    in
    let out:t_Array (t_Array u8 (sz 840)) v_K =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 1) d1
    in
    let out:t_Array (t_Array u8 (sz 840)) v_K =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 2) d2
    in
    out
  | 4uy ->
    let d0, d1, d2, d3:(t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
      t_Array u8 (sz 840)) =
      Libcrux.Hacl.Sha3.Simd256.shake128 (sz 840)
        (Rust_primitives.unsize (input.[ sz 0 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
        (Rust_primitives.unsize (input.[ sz 1 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
        (Rust_primitives.unsize (input.[ sz 2 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
        (Rust_primitives.unsize (input.[ sz 3 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
    in
    let out:t_Array (t_Array u8 (sz 840)) v_K =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 0) d0
    in
    let out:t_Array (t_Array u8 (sz 840)) v_K =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 1) d1
    in
    let out:t_Array (t_Array u8 (sz 840)) v_K =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 2) d2
    in
    let out:t_Array (t_Array u8 (sz 840)) v_K =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 3) d3
    in
    out
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)
