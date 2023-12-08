module Libcrux.Digest
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Rust_primitives
open Core

type t_Algorithm =
  | Algorithm_Sha1 : t_Algorithm
  | Algorithm_Sha224 : t_Algorithm
  | Algorithm_Sha256 : t_Algorithm
  | Algorithm_Sha384 : t_Algorithm
  | Algorithm_Sha512 : t_Algorithm
  | Algorithm_Blake2s : t_Algorithm
  | Algorithm_Blake2b : t_Algorithm
  | Algorithm_Sha3_224_ : t_Algorithm
  | Algorithm_Sha3_256_ : t_Algorithm
  | Algorithm_Sha3_384_ : t_Algorithm
  | Algorithm_Sha3_512_ : t_Algorithm

let digest_size (mode: t_Algorithm) : usize =
  match mode with
  | Algorithm_Sha1  -> sz 20
  | Algorithm_Sha224  -> sz 28
  | Algorithm_Sha256  -> sz 32
  | Algorithm_Sha384  -> sz 48
  | Algorithm_Sha512  -> sz 64
  | Algorithm_Blake2s  -> sz 32
  | Algorithm_Blake2b  -> sz 64
  | Algorithm_Sha3_224_  -> sz 28
  | Algorithm_Sha3_256_  -> sz 32
  | Algorithm_Sha3_384_  -> sz 48
  | Algorithm_Sha3_512_  -> sz 64

val sha3_256_ (payload: t_Slice u8) : t_Array u8 (sz 32)

val sha3_512_ (payload: t_Slice u8) : t_Array u8 (sz 64)

val shake128 (v_LEN: usize) (data: t_Slice u8) : t_Array u8 v_LEN

val shake128x4 (v_LEN: usize) (data0: t_Slice u8) (data1: t_Slice u8) (data2: t_Slice u8) (data3: t_Slice u8): (t_Array u8 v_LEN & t_Array u8 v_LEN & t_Array u8 v_LEN & t_Array u8 v_LEN)

val shake256 (v_LEN: usize) (data: t_Slice u8) : t_Array u8 v_LEN
