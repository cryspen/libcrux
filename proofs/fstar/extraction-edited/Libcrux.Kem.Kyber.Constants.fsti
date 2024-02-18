module Libcrux.Kem.Kyber.Constants
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_BITS_PER_COEFFICIENT: usize = sz 12

let v_COEFFICIENTS_IN_RING_ELEMENT: usize = sz 256

let v_BITS_PER_RING_ELEMENT: usize = v_COEFFICIENTS_IN_RING_ELEMENT *! sz 12

let v_BYTES_PER_RING_ELEMENT: usize = v_BITS_PER_RING_ELEMENT /! sz 8

let v_CPA_PKE_KEY_GENERATION_SEED_SIZE: usize = sz 32

let v_FIELD_MODULUS: i32 = 3329l

let v_H_DIGEST_SIZE: usize = sz 32

let v_REJECTION_SAMPLING_SEED_SIZE: usize = sz 168 *! sz 5

let v_SHARED_SECRET_SIZE: usize = sz 32
