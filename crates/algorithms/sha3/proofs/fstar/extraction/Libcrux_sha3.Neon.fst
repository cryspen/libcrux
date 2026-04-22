module Libcrux_sha3.Neon
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// A SHA3 224 implementation.
let sha224 (digest data: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires (Core_models.Slice.impl__len #u8 digest <: usize) =. mk_usize 28)
      (fun _ -> Prims.l_True) =
  let dummy:t_Array u8 (mk_usize 28) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 28) in
  let (tmp0: t_Slice u8), (tmp1: t_Array u8 (mk_usize 28)) =
    Libcrux_sha3.Generic_keccak.Simd128.keccak2 (mk_usize 144)
      (mk_u8 6)
      (let list = [data; data] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
        Rust_primitives.Hax.array_of_list 2 list)
      digest
      dummy
  in
  let digest:t_Slice u8 = tmp0 in
  let dummy:t_Array u8 (mk_usize 28) = tmp1 in
  let _:Prims.unit = () in
  digest

/// A SHA3 256 implementation.
let sha256 (digest data: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires (Core_models.Slice.impl__len #u8 digest <: usize) =. mk_usize 32)
      (fun _ -> Prims.l_True) =
  let dummy:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
  let (tmp0: t_Slice u8), (tmp1: t_Array u8 (mk_usize 32)) =
    Libcrux_sha3.Generic_keccak.Simd128.keccak2 (mk_usize 136)
      (mk_u8 6)
      (let list = [data; data] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
        Rust_primitives.Hax.array_of_list 2 list)
      digest
      dummy
  in
  let digest:t_Slice u8 = tmp0 in
  let dummy:t_Array u8 (mk_usize 32) = tmp1 in
  let _:Prims.unit = () in
  digest

/// A SHA3 384 implementation.
let sha384 (digest data: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires (Core_models.Slice.impl__len #u8 digest <: usize) =. mk_usize 48)
      (fun _ -> Prims.l_True) =
  let dummy:t_Array u8 (mk_usize 48) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 48) in
  let (tmp0: t_Slice u8), (tmp1: t_Array u8 (mk_usize 48)) =
    Libcrux_sha3.Generic_keccak.Simd128.keccak2 (mk_usize 104)
      (mk_u8 6)
      (let list = [data; data] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
        Rust_primitives.Hax.array_of_list 2 list)
      digest
      dummy
  in
  let digest:t_Slice u8 = tmp0 in
  let dummy:t_Array u8 (mk_usize 48) = tmp1 in
  let _:Prims.unit = () in
  digest

/// A SHA3 512 implementation.
let sha512 (digest data: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires (Core_models.Slice.impl__len #u8 digest <: usize) =. mk_usize 64)
      (fun _ -> Prims.l_True) =
  let dummy:t_Array u8 (mk_usize 64) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 64) in
  let (tmp0: t_Slice u8), (tmp1: t_Array u8 (mk_usize 64)) =
    Libcrux_sha3.Generic_keccak.Simd128.keccak2 (mk_usize 72)
      (mk_u8 6)
      (let list = [data; data] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
        Rust_primitives.Hax.array_of_list 2 list)
      digest
      dummy
  in
  let digest:t_Slice u8 = tmp0 in
  let dummy:t_Array u8 (mk_usize 64) = tmp1 in
  let _:Prims.unit = () in
  digest

/// A SHAKE128 implementation.
let shake128 (v_LEN: usize) (digest: t_Array u8 v_LEN) (data: t_Slice u8) : t_Array u8 v_LEN =
  let dummy:t_Array u8 v_LEN = Rust_primitives.Hax.repeat (mk_u8 0) v_LEN in
  let (tmp0: t_Array u8 v_LEN), (tmp1: t_Array u8 v_LEN) =
    Libcrux_sha3.Generic_keccak.Simd128.keccak2 (mk_usize 168)
      (mk_u8 31)
      (let list = [data; data] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
        Rust_primitives.Hax.array_of_list 2 list)
      digest
      dummy
  in
  let digest:t_Array u8 v_LEN = tmp0 in
  let dummy:t_Array u8 v_LEN = tmp1 in
  let _:Prims.unit = () in
  digest

/// A SHAKE256 implementation.
let shake256 (v_LEN: usize) (digest: t_Array u8 v_LEN) (data: t_Slice u8) : t_Array u8 v_LEN =
  let dummy:t_Array u8 v_LEN = Rust_primitives.Hax.repeat (mk_u8 0) v_LEN in
  let (tmp0: t_Array u8 v_LEN), (tmp1: t_Array u8 v_LEN) =
    Libcrux_sha3.Generic_keccak.Simd128.keccak2 (mk_usize 136)
      (mk_u8 31)
      (let list = [data; data] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
        Rust_primitives.Hax.array_of_list 2 list)
      digest
      dummy
  in
  let digest:t_Array u8 v_LEN = tmp0 in
  let dummy:t_Array u8 v_LEN = tmp1 in
  let _:Prims.unit = () in
  digest
