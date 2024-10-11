module Libcrux_ml_dsa.Ml_dsa_44_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let v_BITS_PER_COMMITMENT_COEFFICIENT: usize = Rust_primitives.mk_usize 6

let v_BITS_PER_ERROR_COEFFICIENT: usize = Rust_primitives.mk_usize 3

let v_BITS_PER_GAMMA1_COEFFICIENT: usize = Rust_primitives.mk_usize 18

let v_COLUMNS_IN_A: usize = Rust_primitives.mk_usize 4

let v_COMMITMENT_HASH_SIZE: usize = Rust_primitives.mk_usize 32

let v_COMMITMENT_RING_ELEMENT_SIZE: usize =
  (v_BITS_PER_COMMITMENT_COEFFICIENT *! Libcrux_ml_dsa.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
    <:
    usize) /!
  Rust_primitives.mk_usize 8

let v_ERROR_RING_ELEMENT_SIZE: usize =
  (v_BITS_PER_ERROR_COEFFICIENT *! Libcrux_ml_dsa.Constants.v_COEFFICIENTS_IN_RING_ELEMENT <: usize) /!
  Rust_primitives.mk_usize 8

let v_ETA: usize = Rust_primitives.mk_usize 2

let v_GAMMA1_EXPONENT: usize = Rust_primitives.mk_usize 17

let v_GAMMA1_RING_ELEMENT_SIZE: usize =
  (v_BITS_PER_GAMMA1_COEFFICIENT *! Libcrux_ml_dsa.Constants.v_COEFFICIENTS_IN_RING_ELEMENT <: usize
  ) /!
  Rust_primitives.mk_usize 8

let v_GAMMA2: i32 =
  (Libcrux_ml_dsa.Constants.v_FIELD_MODULUS -! Rust_primitives.mk_i32 1 <: i32) /!
  Rust_primitives.mk_i32 88

let v_MAX_ONES_IN_HINT: usize = Rust_primitives.mk_usize 80

let v_ONES_IN_VERIFIER_CHALLENGE: usize = Rust_primitives.mk_usize 39

let v_BETA: i32 = cast (v_ONES_IN_VERIFIER_CHALLENGE *! v_ETA <: usize) <: i32

let v_ROWS_IN_A: usize = Rust_primitives.mk_usize 4

let v_COMMITMENT_VECTOR_SIZE: usize = v_COMMITMENT_RING_ELEMENT_SIZE *! v_ROWS_IN_A

let v_SIGNATURE_SIZE: usize =
  ((v_COMMITMENT_HASH_SIZE +! (v_COLUMNS_IN_A *! v_GAMMA1_RING_ELEMENT_SIZE <: usize) <: usize) +!
    v_MAX_ONES_IN_HINT
    <:
    usize) +!
  v_ROWS_IN_A

let v_SIGNING_KEY_SIZE: usize =
  (((Libcrux_ml_dsa.Constants.v_SEED_FOR_A_SIZE +! Libcrux_ml_dsa.Constants.v_SEED_FOR_SIGNING_SIZE
        <:
        usize) +!
      Libcrux_ml_dsa.Constants.v_BYTES_FOR_VERIFICATION_KEY_HASH
      <:
      usize) +!
    ((v_ROWS_IN_A +! v_COLUMNS_IN_A <: usize) *! v_ERROR_RING_ELEMENT_SIZE <: usize)
    <:
    usize) +!
  (v_ROWS_IN_A *! Libcrux_ml_dsa.Constants.v_RING_ELEMENT_OF_T0S_SIZE <: usize)

let v_VERIFICATION_KEY_SIZE: usize =
  Libcrux_ml_dsa.Constants.v_SEED_FOR_A_SIZE +!
  (((Libcrux_ml_dsa.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *! v_ROWS_IN_A <: usize) *!
      (Libcrux_ml_dsa.Constants.v_FIELD_MODULUS_MINUS_ONE_BIT_LENGTH -!
        Libcrux_ml_dsa.Constants.v_BITS_IN_LOWER_PART_OF_T
        <:
        usize)
      <:
      usize) /!
    Rust_primitives.mk_usize 8
    <:
    usize)

/// Sign with ML-DSA 44
/// Sign a `message` with the ML-DSA `signing_key`.
/// This function returns an [`MLDSA44Signature`].
val sign
      (signing_key: Libcrux_ml_dsa.Types.t_MLDSASigningKey (Rust_primitives.mk_usize 2560))
      (message: t_Slice u8)
      (randomness: t_Array u8 (Rust_primitives.mk_usize 32))
    : Prims.Pure
      (Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (Rust_primitives.mk_usize 2420))
          Libcrux_ml_dsa.Ml_dsa_generic.t_SigningError) Prims.l_True (fun _ -> Prims.l_True)

/// Verify an ML-DSA-44 Signature
/// Returns `Ok` when the `signature` is valid for the `message` and
/// `verification_key`, and a [`VerificationError`] otherwise.
val verify
      (verification_key: Libcrux_ml_dsa.Types.t_MLDSAVerificationKey (Rust_primitives.mk_usize 1312)
        )
      (message: t_Slice u8)
      (signature: Libcrux_ml_dsa.Types.t_MLDSASignature (Rust_primitives.mk_usize 2420))
    : Prims.Pure (Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Ml_dsa_generic.t_VerificationError)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Generate an ML-DSA 44 Key Pair
/// Generate an ML-DSA key pair. The input is a byte array of size
/// [`KEY_GENERATION_RANDOMNESS_SIZE`].
/// This function returns an [`MLDSA44KeyPair`].
val generate_key_pair (randomness: t_Array u8 (Rust_primitives.mk_usize 32))
    : Prims.Pure
      (Libcrux_ml_dsa.Types.t_MLDSAKeyPair (Rust_primitives.mk_usize 1312)
          (Rust_primitives.mk_usize 2560)) Prims.l_True (fun _ -> Prims.l_True)
