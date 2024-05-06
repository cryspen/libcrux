module Libcrux_sha3
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let discriminant_Algorithm_Sha3_224_: u32 = 1ul

let discriminant_Algorithm_Sha3_256_: u32 = 2ul

let discriminant_Algorithm_Sha3_384_: u32 = 3ul

/// The Digest Algorithm.
type t_Algorithm =
  | Algorithm_Sha3_224_ : t_Algorithm
  | Algorithm_Sha3_256_ : t_Algorithm
  | Algorithm_Sha3_384_ : t_Algorithm
  | Algorithm_Sha3_512_ : t_Algorithm

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core.Convert.t_From u32 t_Algorithm =
  {
    f_from_pre = (fun (v: t_Algorithm) -> true);
    f_from_post = (fun (v: t_Algorithm) (out: u32) -> true);
    f_from
    =
    fun (v: t_Algorithm) ->
      match v with
      | Algorithm_Sha3_224_  -> 1ul
      | Algorithm_Sha3_256_  -> 2ul
      | Algorithm_Sha3_384_  -> 3ul
      | Algorithm_Sha3_512_  -> 4ul
  }

let discriminant_Algorithm_Sha3_512_: u32 = 4ul

val t_Algorithm_cast_to_repr (x: t_Algorithm) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

unfold
let t_Sha3_224Digest = t_Array u8 (sz 28)

unfold
let t_Sha3_256Digest = t_Array u8 (sz 32)

unfold
let t_Sha3_384Digest = t_Array u8 (sz 48)

unfold
let t_Sha3_512Digest = t_Array u8 (sz 64)

/// Returns the output size of a digest.
val digest_size (mode: t_Algorithm) : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// SHA3
val hash (v_LEN: usize) (algorithm: t_Algorithm) (payload: t_Slice u8)
    : Prims.Pure (t_Array u8 v_LEN) Prims.l_True (fun _ -> Prims.l_True)

/// SHA3 224
val sha224 (payload: t_Slice u8)
    : Prims.Pure (t_Array u8 (sz 28)) Prims.l_True (fun _ -> Prims.l_True)

/// SHA3 224
val sha224_ema (digest payload: t_Slice u8)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

/// SHA3 256
val sha256 (payload: t_Slice u8)
    : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

/// SHA3 256
val sha256_ema (digest payload: t_Slice u8)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

/// SHA3 384
val sha384 (payload: t_Slice u8)
    : Prims.Pure (t_Array u8 (sz 48)) Prims.l_True (fun _ -> Prims.l_True)

/// SHA3 384
val sha384_ema (digest payload: t_Slice u8)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

/// SHA3 512
val sha512 (payload: t_Slice u8)
    : Prims.Pure (t_Array u8 (sz 64)) Prims.l_True (fun _ -> Prims.l_True)

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
      | 1ul -> Algorithm_Sha3_224_ <: t_Algorithm
      | 2ul -> Algorithm_Sha3_256_ <: t_Algorithm
      | 3ul -> Algorithm_Sha3_384_ <: t_Algorithm
      | 4ul -> Algorithm_Sha3_512_ <: t_Algorithm
      | _ ->
        Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.impl_2__new_v1 (Rust_primitives.unsize
                      (let list = ["Unknown Digest mode "] in
                        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                        Rust_primitives.Hax.array_of_list 1 list)
                    <:
                    t_Slice string)
                  (Rust_primitives.unsize (let list =
                          [Core.Fmt.Rt.impl_1__new_display v <: Core.Fmt.Rt.t_Argument]
                        in
                        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                        Rust_primitives.Hax.array_of_list 1 list)
                    <:
                    t_Slice Core.Fmt.Rt.t_Argument)
                <:
                Core.Fmt.t_Arguments)
            <:
            Rust_primitives.Hax.t_Never)
  }
