module Libcrux_sha3.Neon
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_sha3.Simd.Arm64 in
  let open Libcrux_sha3.Traits in
  ()

let keccakx2
      (v_RATE v_SIZE: usize)
      (v_DELIM: u8)
      (data: t_Array (t_Slice u8) (sz 2))
      (out: t_Array (t_Array u8 v_SIZE) (sz 2))
     =
  let hax_temp_output, out:(Prims.unit & t_Array (t_Array u8 v_SIZE) (sz 2)) =
    (),
    Libcrux_sha3.Generic_keccak.keccak (sz 2)
      #Core.Core_arch.Arm_shared.Neon.t_uint64x2_t
      v_RATE
      v_SIZE
      v_DELIM
      data
      out
    <:
    (Prims.unit & t_Array (t_Array u8 v_SIZE) (sz 2))
  in
  out

let sha224 (digest data: t_Slice u8) =
  let out2:t_Array (t_Array u8 (sz 28)) (sz 2) =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat 0uy (sz 28) <: t_Array u8 (sz 28)) (sz 2)
  in
  let out2:t_Array (t_Array u8 (sz 28)) (sz 2) =
    keccakx2 (sz 144)
      (sz 28)
      6uy
      (let list = [data; data] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
        Rust_primitives.Hax.array_of_list 2 list)
      out2
  in
  let digest:t_Slice u8 =
    Core.Slice.impl__copy_from_slice #u8
      digest
      ((out2.[ sz 0 ] <: t_Array u8 (sz 28)).[ {
            Core.Ops.Range.f_start = sz 0;
            Core.Ops.Range.f_end = sz 28
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let hax_temp_output:Prims.unit = () in
  digest

let sha256 (digest data: t_Slice u8) =
  let out2:t_Array (t_Array u8 (sz 32)) (sz 2) =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat 0uy (sz 32) <: t_Array u8 (sz 32)) (sz 2)
  in
  let out2:t_Array (t_Array u8 (sz 32)) (sz 2) =
    keccakx2 (sz 136)
      (sz 32)
      6uy
      (let list = [data; data] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
        Rust_primitives.Hax.array_of_list 2 list)
      out2
  in
  let digest:t_Slice u8 =
    Core.Slice.impl__copy_from_slice #u8
      digest
      ((out2.[ sz 0 ] <: t_Array u8 (sz 32)).[ {
            Core.Ops.Range.f_start = sz 0;
            Core.Ops.Range.f_end = sz 32
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let hax_temp_output:Prims.unit = () in
  digest

let sha384 (digest data: t_Slice u8) =
  let out2:t_Array (t_Array u8 (sz 48)) (sz 2) =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat 0uy (sz 48) <: t_Array u8 (sz 48)) (sz 2)
  in
  let out2:t_Array (t_Array u8 (sz 48)) (sz 2) =
    keccakx2 (sz 104)
      (sz 48)
      6uy
      (let list = [data; data] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
        Rust_primitives.Hax.array_of_list 2 list)
      out2
  in
  let digest:t_Slice u8 =
    Core.Slice.impl__copy_from_slice #u8
      digest
      ((out2.[ sz 0 ] <: t_Array u8 (sz 48)).[ {
            Core.Ops.Range.f_start = sz 0;
            Core.Ops.Range.f_end = sz 48
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let hax_temp_output:Prims.unit = () in
  digest

let sha512 (digest data: t_Slice u8) =
  let out2:t_Array (t_Array u8 (sz 64)) (sz 2) =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat 0uy (sz 64) <: t_Array u8 (sz 64)) (sz 2)
  in
  let out2:t_Array (t_Array u8 (sz 64)) (sz 2) =
    keccakx2 (sz 72)
      (sz 64)
      6uy
      (let list = [data; data] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
        Rust_primitives.Hax.array_of_list 2 list)
      out2
  in
  let digest:t_Slice u8 =
    Core.Slice.impl__copy_from_slice #u8
      digest
      ((out2.[ sz 0 ] <: t_Array u8 (sz 64)).[ {
            Core.Ops.Range.f_start = sz 0;
            Core.Ops.Range.f_end = sz 64
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let hax_temp_output:Prims.unit = () in
  digest

let shake128 (v_LEN: usize) (digest: t_Array u8 v_LEN) (data: t_Slice u8) =
  let out2:t_Array (t_Array u8 v_LEN) (sz 2) =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat 0uy v_LEN <: t_Array u8 v_LEN) (sz 2)
  in
  let out2:t_Array (t_Array u8 v_LEN) (sz 2) =
    keccakx2 (sz 168)
      v_LEN
      31uy
      (let list = [data; data] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
        Rust_primitives.Hax.array_of_list 2 list)
      out2
  in
  let digest:t_Array u8 v_LEN =
    Core.Slice.impl__copy_from_slice #u8
      digest
      ((out2.[ sz 0 ] <: t_Array u8 v_LEN).[ {
            Core.Ops.Range.f_start = sz 0;
            Core.Ops.Range.f_end = v_LEN
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let hax_temp_output:Prims.unit = () in
  digest

let shake256 (v_LEN: usize) (digest: t_Array u8 v_LEN) (data: t_Slice u8) =
  let out2:t_Array (t_Array u8 v_LEN) (sz 2) =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat 0uy v_LEN <: t_Array u8 v_LEN) (sz 2)
  in
  let out2:t_Array (t_Array u8 v_LEN) (sz 2) =
    keccakx2 (sz 136)
      v_LEN
      31uy
      (let list = [data; data] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
        Rust_primitives.Hax.array_of_list 2 list)
      out2
  in
  let digest:t_Array u8 v_LEN =
    Core.Slice.impl__copy_from_slice #u8
      digest
      ((out2.[ sz 0 ] <: t_Array u8 v_LEN).[ {
            Core.Ops.Range.f_start = sz 0;
            Core.Ops.Range.f_end = v_LEN
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let hax_temp_output:Prims.unit = () in
  digest
