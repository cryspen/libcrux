module Libcrux.Kem.Kyber.Constants
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let v_FIELD_MODULUS: i32 = 3329l

let v_BITS_PER_COEFFICIENT: usize = 12sz

let v_COEFFICIENTS_IN_RING_ELEMENT: usize = 256sz

let v_BITS_PER_RING_ELEMENT: usize = v_COEFFICIENTS_IN_RING_ELEMENT *. 12sz

let v_BYTES_PER_RING_ELEMENT: usize = v_BITS_PER_RING_ELEMENT /. 8sz

let v_REJECTION_SAMPLING_SEED_SIZE: usize = 168sz *. 5sz

let v_SHARED_SECRET_SIZE: usize = 32sz

let v_CPA_PKE_KEY_GENERATION_SEED_SIZE: usize = 32sz

let v_H_DIGEST_SIZE: usize = Libcrux.Digest.digest_size Libcrux.Digest.Algorithm_Sha3_256_