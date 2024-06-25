module Libcrux_sha3.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_sha3.Portable_keccak in
  let open Libcrux_sha3.Traits in
  ()

let keccakx1 (v_RATE v_SIZE: usize) (v_DELIM: u8) (data out: t_Slice u8) : t_Slice u8 =
  let out1:t_Array (t_Array u8 v_SIZE) (sz 1) =
    let list = [Rust_primitives.Hax.repeat 0uy v_SIZE] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
    Rust_primitives.Hax.array_of_list 1 list
  in
  let out1:t_Array (t_Array u8 v_SIZE) (sz 1) =
    Libcrux_sha3.Generic_keccak.keccak (sz 1)
      #u64
      v_RATE
      v_SIZE
      v_DELIM
      (let list = [data] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
        Rust_primitives.Hax.array_of_list 1 list)
      out1
  in
  let out:t_Slice u8 =
    Core.Slice.impl__copy_from_slice #u8
      out
      ((out1.[ sz 0 ] <: t_Array u8 v_SIZE).[ {
            Core.Ops.Range.f_start = sz 0;
            Core.Ops.Range.f_end = v_SIZE
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  out

/// A portable SHA3 224 implementation.
let sha224 (digest data: t_Slice u8) : t_Slice u8 =
  let digest:t_Slice u8 = keccakx1 (sz 144) (sz 28) 6uy data digest in
  digest

/// A portable SHA3 256 implementation.
let sha256 (digest data: t_Slice u8) : t_Slice u8 =
  let digest:t_Slice u8 = keccakx1 (sz 136) (sz 32) 6uy data digest in
  digest

/// A portable SHA3 384 implementation.
let sha384 (digest data: t_Slice u8) : t_Slice u8 =
  let digest:t_Slice u8 = keccakx1 (sz 104) (sz 48) 6uy data digest in
  digest

/// A portable SHA3 512 implementation.
let sha512 (digest data: t_Slice u8) : t_Slice u8 =
  let digest:t_Slice u8 = keccakx1 (sz 72) (sz 64) 6uy data digest in
  digest

/// A portable SHAKE128 implementation.
let shake128 (v_SIZE: usize) (digest data: t_Slice u8) : t_Slice u8 =
  let digest:t_Slice u8 = keccakx1 (sz 168) v_SIZE 31uy data digest in
  digest

/// A portable SHAKE256 implementation.
let shake256 (v_SIZE: usize) (digest data: t_Slice u8) : t_Slice u8 =
  let digest:t_Slice u8 = keccakx1 (sz 136) v_SIZE 31uy data digest in
  digest

type t_KeccakState1 = { f_state:Libcrux_sha3.Generic_keccak.t_KeccakState (sz 1) u64 }
