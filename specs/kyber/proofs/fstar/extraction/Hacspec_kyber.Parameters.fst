module Hacspec_kyber.Parameters
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_BITS_PER_COEFFICIENT: usize = sz 12

let v_COEFFICIENTS_IN_RING_ELEMENT: usize = sz 256

let v_BITS_PER_RING_ELEMENT: usize = v_COEFFICIENTS_IN_RING_ELEMENT *! sz 12

let v_BYTES_PER_RING_ELEMENT: usize = v_BITS_PER_RING_ELEMENT /! sz 8

let v_CPA_PKE_KEY_GENERATION_SEED_SIZE: usize = sz 32

let v_CPA_PKE_MESSAGE_SIZE: usize = sz 32

let v_FIELD_MODULUS: u16 = 3329us

let v_RANK: usize = sz 3

let v_CPA_PKE_SECRET_KEY_SIZE: usize =
  ((v_RANK *! v_COEFFICIENTS_IN_RING_ELEMENT <: usize) *! v_BITS_PER_COEFFICIENT <: usize) /! sz 8

let v_T_AS_NTT_ENCODED_SIZE: usize =
  ((v_RANK *! v_COEFFICIENTS_IN_RING_ELEMENT <: usize) *! v_BITS_PER_COEFFICIENT <: usize) /! sz 8

let v_CPA_PKE_PUBLIC_KEY_SIZE: usize = v_T_AS_NTT_ENCODED_SIZE +! sz 32

let v_VECTOR_U_COMPRESSION_FACTOR: usize = sz 10

let v_VECTOR_U_ENCODED_SIZE: usize =
  ((v_RANK *! v_COEFFICIENTS_IN_RING_ELEMENT <: usize) *! v_VECTOR_U_COMPRESSION_FACTOR <: usize) /!
  sz 8

let v_VECTOR_V_COMPRESSION_FACTOR: usize = sz 4

let v_VECTOR_V_ENCODED_SIZE: usize =
  (v_COEFFICIENTS_IN_RING_ELEMENT *! v_VECTOR_V_COMPRESSION_FACTOR <: usize) /! sz 8

let v_CPA_PKE_CIPHERTEXT_SIZE: usize = v_VECTOR_U_ENCODED_SIZE +! v_VECTOR_V_ENCODED_SIZE
