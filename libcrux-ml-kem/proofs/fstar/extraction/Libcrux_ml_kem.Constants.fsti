module Libcrux_ml_kem.Constants
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

/// Each field element needs floor(log_2(FIELD_MODULUS)) + 1 = 12 bits to represent
let v_BITS_PER_COEFFICIENT: usize = Rust_primitives.mk_usize 12

/// Coefficients per ring element
let v_COEFFICIENTS_IN_RING_ELEMENT: usize = Rust_primitives.mk_usize 256

/// Bits required per (uncompressed) ring element
let v_BITS_PER_RING_ELEMENT: usize = v_COEFFICIENTS_IN_RING_ELEMENT *! Rust_primitives.mk_usize 12

/// Bytes required per (uncompressed) ring element
let v_BYTES_PER_RING_ELEMENT: usize = v_BITS_PER_RING_ELEMENT /! Rust_primitives.mk_usize 8

let v_CPA_PKE_KEY_GENERATION_SEED_SIZE: usize = Rust_primitives.mk_usize 32

/// SHA3 512 digest size
let v_G_DIGEST_SIZE: usize = Rust_primitives.mk_usize 64

/// SHA3 256 digest size
let v_H_DIGEST_SIZE: usize = Rust_primitives.mk_usize 32

/// The size of an ML-KEM shared secret.
let v_SHARED_SECRET_SIZE: usize = Rust_primitives.mk_usize 32
