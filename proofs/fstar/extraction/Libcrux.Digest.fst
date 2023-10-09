module Libcrux.Digest
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
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

let sha3_256_ (payload: slice u8) : array u8 (sz 32) = Libcrux.Hacl.Sha3.sha256 payload

let sha3_512_ (payload: slice u8) : array u8 (sz 64) = Libcrux.Hacl.Sha3.sha512 payload

let shake128 (#v_LEN: usize) (data: slice u8) : array u8 v_LEN = Libcrux.Hacl.Sha3.shake128 data

let shake256 (#v_LEN: usize) (data: slice u8) : array u8 v_LEN = Libcrux.Hacl.Sha3.shake256 data