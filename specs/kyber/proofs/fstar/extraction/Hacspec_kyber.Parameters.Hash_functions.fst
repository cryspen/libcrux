module Hacspec_kyber.Parameters.Hash_functions
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_H_DIGEST_SIZE: usize =
  Libcrux.Digest.digest_size (Libcrux.Digest.Algorithm_Sha3_256_ <: Libcrux.Digest.t_Algorithm)

let v_H (input: t_Slice u8) : t_Array u8 (sz 32) = Libcrux.Digest.sha3_256_ input

let v_G (input: t_Slice u8) : t_Array u8 (sz 64) = Libcrux.Digest.sha3_512_ input

let v_XOF (v_LEN: usize) (input: t_Slice u8) : t_Array u8 v_LEN =
  Libcrux.Digest.shake128 v_LEN input

let v_J (v_LEN: usize) (input: t_Slice u8) : t_Array u8 v_LEN = Libcrux.Digest.shake256 v_LEN input

let v_PRF (v_LEN: usize) (input: t_Slice u8) : t_Array u8 v_LEN =
  Libcrux.Digest.shake256 v_LEN input
