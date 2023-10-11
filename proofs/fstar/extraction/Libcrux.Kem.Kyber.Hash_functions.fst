module Libcrux.Kem.Kyber.Hash_functions
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let v_G (input: slice u8) : array u8 (sz 64) = Libcrux.Digest.sha3_512_ input

let v_H (input: slice u8) : array u8 (sz 32) = Libcrux.Digest.sha3_256_ input

let v_PRF (#v_LEN: usize) (input: slice u8) : array u8 v_LEN = Libcrux.Digest.shake256 input

let v_XOFx4 (#v_LEN #v_K: usize) (input: array (array u8 (sz 34)) v_K) : array (array u8 v_LEN) v_K =
  let out:array (array u8 v_LEN) v_K =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat 0uy v_LEN <: array u8 v_LEN) v_K
  in
  let out:array (array u8 v_LEN) v_K =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K
            })
        <:
        (Core.Iter.Traits.Collect.impl (Core.Ops.Range.t_Range usize)).f_IntoIter)
      out
      (fun out i ->
          Rust_primitives.Hax.update_at out
            i
            (Libcrux.Digest.shake128 (Rust_primitives.unsize (input.[ i ] <: array u8 (sz 34))
                  <:
                  slice u8)
              <:
              array u8 v_LEN)
          <:
          array (array u8 v_LEN) v_K)
  in
  out

let v_KDF (#v_LEN: usize) (input: slice u8) : array u8 v_LEN = Libcrux.Digest.shake256 input