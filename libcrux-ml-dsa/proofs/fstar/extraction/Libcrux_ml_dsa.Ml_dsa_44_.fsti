module Libcrux_ml_dsa.Ml_dsa_44_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let v_BITS_PER_COMMITMENT_COEFFICIENT: usize = sz 6

let v_BITS_PER_ERROR_COEFFICIENT: usize = sz 3

let v_BITS_PER_GAMMA1_COEFFICIENT: usize = sz 18

let v_COLUMNS_IN_A: usize = sz 4

let v_COMMITMENT_HASH_SIZE: usize = sz 32

let v_COMMITMENT_RING_ELEMENT_SIZE: usize =
  (v_BITS_PER_COMMITMENT_COEFFICIENT *! Libcrux_ml_dsa.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
    <:
    usize) /!
  sz 8

let v_ERROR_RING_ELEMENT_SIZE: usize =
  (v_BITS_PER_ERROR_COEFFICIENT *! Libcrux_ml_dsa.Constants.v_COEFFICIENTS_IN_RING_ELEMENT <: usize) /!
  sz 8

let v_ETA: usize = sz 2

let v_GAMMA1_EXPONENT: usize = sz 17

let v_GAMMA1_RING_ELEMENT_SIZE: usize =
  (v_BITS_PER_GAMMA1_COEFFICIENT *! Libcrux_ml_dsa.Constants.v_COEFFICIENTS_IN_RING_ELEMENT <: usize
  ) /!
  sz 8

let v_GAMMA2: i32 = (Libcrux_ml_dsa.Constants.v_FIELD_MODULUS -! 1l <: i32) /! 88l

let v_MAX_ONES_IN_HINT: usize = sz 80

let v_ONES_IN_VERIFIER_CHALLENGE: usize = sz 39

let v_BETA: i32 = cast (v_ONES_IN_VERIFIER_CHALLENGE *! v_ETA <: usize) <: i32

let v_ROWS_IN_A: usize = sz 4

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
    sz 8
    <:
    usize)

/// Sign with ML-DSA 44
/// Sign a `message` with the ML-DSA `signing_key`.
/// This function returns an [`MLDSA44Signature`].
val sign
      (signing_key: Libcrux_ml_dsa.Types.t_MLDSASigningKey (sz 2560))
      (message: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
    : Prims.Pure
      (Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (sz 2420))
          Libcrux_ml_dsa.Ml_dsa_generic.t_SigningError) Prims.l_True (fun _ -> Prims.l_True)

/// Verify an ML-DSA-44 Signature
/// Returns `Ok` when the `signature` is valid for the `message` and
/// `verification_key`, and a [`VerificationError`] otherwise.
val verify
      (verification_key: Libcrux_ml_dsa.Types.t_MLDSAVerificationKey (sz 1312))
      (message: t_Slice u8)
      (signature: Libcrux_ml_dsa.Types.t_MLDSASignature (sz 2420))
    : Prims.Pure (Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Ml_dsa_generic.t_VerificationError)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Generate an ML-DSA 44 Key Pair
/// Generate an ML-DSA key pair. The input is a byte array of size
/// [`KEY_GENERATION_RANDOMNESS_SIZE`].
/// This function returns an [`MLDSA44KeyPair`].
val generate_key_pair (randomness: t_Array u8 (sz 32))
    : Prims.Pure (Libcrux_ml_dsa.Types.t_MLDSAKeyPair (sz 1312) (sz 2560))
      Prims.l_True
      (fun _ -> Prims.l_True)
