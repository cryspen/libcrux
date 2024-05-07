module Libcrux.Kem.Kyber.Constants
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// Each field element needs floor(log_2(FIELD_MODULUS)) + 1 = 12 bits to represent
let v_BITS_PER_COEFFICIENT: usize = sz 12

/// Coefficients per ring element
let v_COEFFICIENTS_IN_RING_ELEMENT: usize = sz 256

/// Bits required per (uncompressed) ring element
let v_BITS_PER_RING_ELEMENT: usize = v_COEFFICIENTS_IN_RING_ELEMENT *! sz 12

/// Bytes required per (uncompressed) ring element
let v_BYTES_PER_RING_ELEMENT: usize = v_BITS_PER_RING_ELEMENT /! sz 8

let v_CPA_PKE_KEY_GENERATION_SEED_SIZE: usize = sz 32

/// Field modulus: 3329
let v_FIELD_MODULUS: i32 = 3329l

let v_H_DIGEST_SIZE: usize = sz 32

/// PKE message size
let v_SHARED_SECRET_SIZE: usize = sz 32
