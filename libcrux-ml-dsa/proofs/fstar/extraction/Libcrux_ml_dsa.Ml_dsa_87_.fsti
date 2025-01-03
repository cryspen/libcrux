module Libcrux_ml_dsa.Ml_dsa_87_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let v_BITS_PER_COMMITMENT_COEFFICIENT: usize = sz 4

let v_BITS_PER_ERROR_COEFFICIENT: usize = sz 3

let v_BITS_PER_GAMMA1_COEFFICIENT: usize = sz 20

let v_COLUMNS_IN_A: usize = sz 7

let v_COMMITMENT_HASH_SIZE: usize = sz 64

let v_COMMITMENT_RING_ELEMENT_SIZE: usize =
  (v_BITS_PER_COMMITMENT_COEFFICIENT *! Libcrux_ml_dsa.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
    <:
    usize) /!
  sz 8

let v_ERROR_RING_ELEMENT_SIZE: usize =
  (v_BITS_PER_ERROR_COEFFICIENT *! Libcrux_ml_dsa.Constants.v_COEFFICIENTS_IN_RING_ELEMENT <: usize) /!
  sz 8

let v_ETA: usize = sz 2

let v_GAMMA1_EXPONENT: usize = sz 19

let v_GAMMA1_RING_ELEMENT_SIZE: usize =
  (v_BITS_PER_GAMMA1_COEFFICIENT *! Libcrux_ml_dsa.Constants.v_COEFFICIENTS_IN_RING_ELEMENT <: usize
  ) /!
  sz 8

let v_GAMMA2: i32 = (Libcrux_ml_dsa.Constants.v_FIELD_MODULUS -! 1l <: i32) /! 32l

let v_MAX_ONES_IN_HINT: usize = sz 75

let v_ONES_IN_VERIFIER_CHALLENGE: usize = sz 60

let v_BETA: i32 = cast (v_ONES_IN_VERIFIER_CHALLENGE *! v_ETA <: usize) <: i32

let v_ROWS_IN_A: usize = sz 8

let v_COMMITMENT_VECTOR_SIZE: usize = v_COMMITMENT_RING_ELEMENT_SIZE *! v_ROWS_IN_A

let v_ROWS_X_COLUMNS: usize = v_ROWS_IN_A *! v_COLUMNS_IN_A

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

/// Generate an ML-DSA 87 Key Pair
/// Generate an ML-DSA key pair. The input is a byte array of size
/// [`KEY_GENERATION_RANDOMNESS_SIZE`].
/// This function returns an [`MLDSA87KeyPair`].
val generate_key_pair (randomness: t_Array u8 (sz 32))
    : Prims.Pure (Libcrux_ml_dsa.Types.t_MLDSAKeyPair (sz 2592) (sz 4896))
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Sign with ML-DSA 87
/// Sign a `message` with the ML-DSA `signing_key`.
/// The parameter `context` is used for domain separation
/// and is a byte string of length at most 255 bytes. It
/// may also be empty.
/// This function returns an [`MLDSA87Signature`].
val sign
      (signing_key: Libcrux_ml_dsa.Types.t_MLDSASigningKey (sz 4896))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
    : Prims.Pure
      (Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (sz 4627))
          Libcrux_ml_dsa.Types.t_SigningError) Prims.l_True (fun _ -> Prims.l_True)

/// Sign with HashML-DSA 87, with a SHAKE128 pre-hashing
/// Sign a digest of `message` derived using `pre_hash` with the
/// ML-DSA `signing_key`.
/// The parameter `context` is used for domain separation
/// and is a byte string of length at most 255 bytes. It
/// may also be empty.
/// This function returns an [`MLDSA87Signature`].
val sign_pre_hashed_shake128
      (signing_key: Libcrux_ml_dsa.Types.t_MLDSASigningKey (sz 4896))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
    : Prims.Pure
      (Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (sz 4627))
          Libcrux_ml_dsa.Types.t_SigningError) Prims.l_True (fun _ -> Prims.l_True)

/// Verify an ML-DSA-87 Signature
/// The parameter `context` is used for domain separation
/// and is a byte string of length at most 255 bytes. It
/// may also be empty.
/// Returns `Ok` when the `signature` is valid for the `message` and
/// `verification_key`, and a [`VerificationError`] otherwise.
val verify
      (verification_key: Libcrux_ml_dsa.Types.t_MLDSAVerificationKey (sz 2592))
      (message context: t_Slice u8)
      (signature: Libcrux_ml_dsa.Types.t_MLDSASignature (sz 4627))
    : Prims.Pure (Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Verify a HashML-DSA-87 Signature, with a SHAKE128 pre-hashing
/// The parameter `context` is used for domain separation
/// and is a byte string of length at most 255 bytes. It
/// may also be empty.
/// Returns `Ok` when the `signature` is valid for the `message` and
/// `verification_key`, and a [`VerificationError`] otherwise.
val verify_pre_hashed_shake128
      (verification_key: Libcrux_ml_dsa.Types.t_MLDSAVerificationKey (sz 2592))
      (message context: t_Slice u8)
      (signature: Libcrux_ml_dsa.Types.t_MLDSASignature (sz 4627))
    : Prims.Pure (Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError)
      Prims.l_True
      (fun _ -> Prims.l_True)
