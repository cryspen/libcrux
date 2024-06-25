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

val keccakx2
      (v_RATE v_SIZE: usize)
      (v_DELIM: u8)
      (data: t_Array (t_Slice u8) (sz 2))
      (out: t_Array (t_Array u8 v_SIZE) (sz 2))
    : Prims.Pure (t_Array (t_Array u8 v_SIZE) (sz 2)) Prims.l_True (fun _ -> Prims.l_True)

/// A portable SHA3 224 implementation.
val sha224 (digest data: t_Slice u8) : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

/// A portable SHA3 256 implementation.
val sha256 (digest data: t_Slice u8) : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

/// A portable SHA3 384 implementation.
val sha384 (digest data: t_Slice u8) : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

/// A portable SHA3 512 implementation.
val sha512 (digest data: t_Slice u8) : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

/// A portable SHAKE128 implementation.
val shake128 (v_LEN: usize) (digest: t_Array u8 v_LEN) (data: t_Slice u8)
    : Prims.Pure (t_Array u8 v_LEN) Prims.l_True (fun _ -> Prims.l_True)

/// A portable SHAKE256 implementation.
val shake256 (v_LEN: usize) (digest: t_Array u8 v_LEN) (data: t_Slice u8)
    : Prims.Pure (t_Array u8 v_LEN) Prims.l_True (fun _ -> Prims.l_True)
