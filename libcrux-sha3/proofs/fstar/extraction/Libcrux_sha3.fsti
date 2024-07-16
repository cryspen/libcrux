module Libcrux_sha3
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let discriminant_Algorithm_Sha224: u32 = 1ul

let discriminant_Algorithm_Sha256: u32 = 2ul

let discriminant_Algorithm_Sha384: u32 = 3ul

/// The Digest Algorithm.
type t_Algorithm =
  | Algorithm_Sha224 : t_Algorithm
  | Algorithm_Sha256 : t_Algorithm
  | Algorithm_Sha384 : t_Algorithm
  | Algorithm_Sha512 : t_Algorithm

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core.Convert.t_From u32 t_Algorithm =
  {
    f_from_pre = (fun (v: t_Algorithm) -> true);
    f_from_post = (fun (v: t_Algorithm) (out: u32) -> true);
    f_from
    =
    fun (v: t_Algorithm) ->
      match v with
      | Algorithm_Sha224  -> 1ul
      | Algorithm_Sha256  -> 2ul
      | Algorithm_Sha384  -> 3ul
      | Algorithm_Sha512  -> 4ul
  }

let discriminant_Algorithm_Sha512: u32 = 4ul

val t_Algorithm_cast_to_repr (x: t_Algorithm) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val from__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

/// Returns the output size of a digest.
val digest_size (mode: t_Algorithm) : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// SHA3
val hash (v_LEN: usize) (algorithm: t_Algorithm) (payload: t_Slice u8)
    : Prims.Pure (t_Array u8 v_LEN) Prims.l_True (fun _ -> Prims.l_True)

/// SHA3 224
val sha224 (data: t_Slice u8) : Prims.Pure (t_Array u8 (sz 28)) Prims.l_True (fun _ -> Prims.l_True)

/// SHA3 224
/// Preconditions:
/// - `digest.len() == 28`
val sha224_ema (digest payload: t_Slice u8)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

/// SHA3 256
val sha256 (data: t_Slice u8) : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

/// SHA3 256
val sha256_ema (digest payload: t_Slice u8)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

/// SHA3 384
val sha384 (data: t_Slice u8) : Prims.Pure (t_Array u8 (sz 48)) Prims.l_True (fun _ -> Prims.l_True)

/// SHA3 384
val sha384_ema (digest payload: t_Slice u8)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

/// SHA3 512
val sha512 (data: t_Slice u8) : Prims.Pure (t_Array u8 (sz 64)) Prims.l_True (fun _ -> Prims.l_True)

/// SHA3 512
val sha512_ema (digest payload: t_Slice u8)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

/// SHAKE 128
val shake128 (v_BYTES: usize) (data: t_Slice u8)
    : Prims.Pure (t_Array u8 v_BYTES) Prims.l_True (fun _ -> Prims.l_True)

/// SHAKE 256
/// Note that the output length `BYTES` must fit into 32 bit. If it is longer,
/// the output will only return `u32::MAX` bytes.
val shake256 (v_BYTES: usize) (data: t_Slice u8)
    : Prims.Pure (t_Array u8 v_BYTES) Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core.Convert.t_From t_Algorithm u32 =
  {
    f_from_pre = (fun (v: u32) -> true);
    f_from_post = (fun (v: u32) (out: t_Algorithm) -> true);
    f_from
    =
    fun (v: u32) ->
      match v with
      | 1ul -> Algorithm_Sha224 <: t_Algorithm
      | 2ul -> Algorithm_Sha256 <: t_Algorithm
      | 3ul -> Algorithm_Sha384 <: t_Algorithm
      | 4ul -> Algorithm_Sha512 <: t_Algorithm
      | _ ->
        Rust_primitives.Hax.never_to_any (from__panic_cold_explicit ()
            <:
            Rust_primitives.Hax.t_Never)
  }
