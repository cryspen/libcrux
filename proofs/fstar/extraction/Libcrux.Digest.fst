module Libcrux.Digest

open Rust_primitives

type alg = | Algorithm_Sha3_256_
let digest_size x = sz 32

let sha3_512_ x = x
let sha3_256_ x = x
let shake256 x = x
let shake128 x = x
