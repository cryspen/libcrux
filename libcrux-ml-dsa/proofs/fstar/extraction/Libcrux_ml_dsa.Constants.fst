module Libcrux_ml_dsa.Constants
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_BITS_IN_LOWER_PART_OF_T: usize = Rust_primitives.mk_usize 13

let v_BYTES_FOR_VERIFICATION_KEY_HASH: usize = Rust_primitives.mk_usize 64

let v_COEFFICIENTS_IN_RING_ELEMENT: usize = Rust_primitives.mk_usize 256

/// The length of `context` is serialized to a single `u8`.
let v_CONTEXT_MAX_LEN: usize = Rust_primitives.mk_usize 255

let v_FIELD_MODULUS: i32 = Rust_primitives.mk_i32 8380417

let v_FIELD_MODULUS_MINUS_ONE_BIT_LENGTH: usize = Rust_primitives.mk_usize 23

let v_BITS_IN_UPPER_PART_OF_T: usize =
  v_FIELD_MODULUS_MINUS_ONE_BIT_LENGTH -! v_BITS_IN_LOWER_PART_OF_T

/// Number of bytes of entropy required for key generation.
let v_KEY_GENERATION_RANDOMNESS_SIZE: usize = Rust_primitives.mk_usize 32

let v_MASK_SEED_SIZE: usize = Rust_primitives.mk_usize 64

let v_MESSAGE_REPRESENTATIVE_SIZE: usize = Rust_primitives.mk_usize 64

let v_REJECTION_SAMPLE_BOUND_SIGN: usize = Rust_primitives.mk_usize 814

let v_RING_ELEMENT_OF_T0S_SIZE: usize =
  (v_BITS_IN_LOWER_PART_OF_T *! v_COEFFICIENTS_IN_RING_ELEMENT <: usize) /!
  Rust_primitives.mk_usize 8

let v_RING_ELEMENT_OF_T1S_SIZE: usize =
  (v_BITS_IN_UPPER_PART_OF_T *! v_COEFFICIENTS_IN_RING_ELEMENT <: usize) /!
  Rust_primitives.mk_usize 8

let v_SEED_FOR_A_SIZE: usize = Rust_primitives.mk_usize 32

let v_SEED_FOR_ERROR_VECTORS_SIZE: usize = Rust_primitives.mk_usize 64

let v_SEED_FOR_SIGNING_SIZE: usize = Rust_primitives.mk_usize 32

/// Number of bytes of entropy required for signing.
let v_SIGNING_RANDOMNESS_SIZE: usize = Rust_primitives.mk_usize 32
