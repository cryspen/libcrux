module Libcrux.Kem.Kyber.Hash_functions
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let v_G (input: slice u8) : array u8 64sz = Libcrux.Digest.sha3_512_ input

let v_H (input: slice u8) : array u8 32sz = Libcrux.Digest.sha3_256_ input

let v_PRF (#len: usize) (input: slice u8) : array u8 v_LEN = Libcrux.Digest.shake256 input

let v_XOFx4 (#len #k: usize) (input: array (array u8 34sz) v_K) : array (array u8 v_LEN) v_K =
  let out:array (array u8 v_LEN) v_K =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat 0uy v_LEN <: array u8 v_LEN) v_K
  in
  let out:array (array u8 v_LEN) v_K =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = v_K
            })
        <:
        _)
      out
      (fun out i ->
          Rust_primitives.Hax.update_at out
            i
            (Libcrux.Digest.shake128 (Rust_primitives.unsize (input.[ i ] <: array u8 34sz)
                  <:
                  slice u8)
              <:
              array u8 v_LEN)
          <:
          array (array u8 v_LEN) v_K)
  in
  out

let v_KDF (#len: usize) (input: slice u8) : array u8 v_LEN = Libcrux.Digest.shake256 input