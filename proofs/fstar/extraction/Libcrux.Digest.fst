module Libcrux.Digest

open Rust_primitives

type alg = | Algorithm_Sha3_256_
let digest_size x = sz 32
