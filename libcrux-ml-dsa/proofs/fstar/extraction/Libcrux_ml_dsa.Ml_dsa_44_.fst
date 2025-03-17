module Libcrux_ml_dsa.Ml_dsa_44_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

/// Generate an ML-DSA 44 Key Pair
/// Generate an ML-DSA key pair. The input is a byte array of size
/// [`KEY_GENERATION_RANDOMNESS_SIZE`].
/// This function returns an [`MLDSA44KeyPair`].
let generate_key_pair (randomness: t_Array u8 (mk_usize 32))
    : Libcrux_ml_dsa.Types.t_MLDSAKeyPair (mk_usize 1312) (mk_usize 2560) =
  let signing_key:t_Array u8 (mk_usize 2560) =
    Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 2560)
  in
  let verification_key:t_Array u8 (mk_usize 1312) =
    Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 1312)
  in
  let tmp0, tmp1:(t_Array u8 (mk_usize 2560) & t_Array u8 (mk_usize 1312)) =
    Libcrux_ml_dsa.Ml_dsa_generic.Multiplexing.Ml_dsa_44_.generate_key_pair randomness
      signing_key
      verification_key
  in
  let signing_key:t_Array u8 (mk_usize 2560) = tmp0 in
  let verification_key:t_Array u8 (mk_usize 1312) = tmp1 in
  let _:Prims.unit = () in
  {
    Libcrux_ml_dsa.Types.f_signing_key = Libcrux_ml_dsa.Types.impl__new (mk_usize 2560) signing_key;
    Libcrux_ml_dsa.Types.f_verification_key
    =
    Libcrux_ml_dsa.Types.impl_2__new (mk_usize 1312) verification_key
  }
  <:
  Libcrux_ml_dsa.Types.t_MLDSAKeyPair (mk_usize 1312) (mk_usize 2560)

/// Sign with ML-DSA 44
/// Sign a `message` with the ML-DSA `signing_key`.
/// The parameter `context` is used for domain separation
/// and is a byte string of length at most 255 bytes. It
/// may also be empty.
/// This function returns an [`MLDSA44Signature`].
let sign
      (signing_key: Libcrux_ml_dsa.Types.t_MLDSASigningKey (mk_usize 2560))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (mk_usize 32))
    : Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (mk_usize 2420))
      Libcrux_ml_dsa.Types.t_SigningError =
  Libcrux_ml_dsa.Ml_dsa_generic.Multiplexing.Ml_dsa_44_.sign (Libcrux_ml_dsa.Types.impl__as_ref (mk_usize
          2560)
        signing_key
      <:
      t_Array u8 (mk_usize 2560))
    message
    context
    randomness

/// Verify an ML-DSA-44 Signature
/// The parameter `context` is used for domain separation
/// and is a byte string of length at most 255 bytes. It
/// may also be empty.
/// Returns `Ok` when the `signature` is valid for the `message` and
/// `verification_key`, and a [`VerificationError`] otherwise.
let verify
      (verification_key: Libcrux_ml_dsa.Types.t_MLDSAVerificationKey (mk_usize 1312))
      (message context: t_Slice u8)
      (signature: Libcrux_ml_dsa.Types.t_MLDSASignature (mk_usize 2420))
    : Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError =
  Libcrux_ml_dsa.Ml_dsa_generic.Multiplexing.Ml_dsa_44_.verify (Libcrux_ml_dsa.Types.impl_2__as_ref (
          mk_usize 1312)
        verification_key
      <:
      t_Array u8 (mk_usize 1312))
    message
    context
    (Libcrux_ml_dsa.Types.impl_4__as_ref (mk_usize 2420) signature <: t_Array u8 (mk_usize 2420))

/// Sign with HashML-DSA 44, with a SHAKE128 pre-hashing
/// Sign a digest of `message` derived using `pre_hash` with the
/// ML-DSA `signing_key`.
/// The parameter `context` is used for domain separation
/// and is a byte string of length at most 255 bytes. It
/// may also be empty.
/// This function returns an [`MLDSA44Signature`].
let sign_pre_hashed_shake128
      (signing_key: Libcrux_ml_dsa.Types.t_MLDSASigningKey (mk_usize 2560))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (mk_usize 32))
    : Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (mk_usize 2420))
      Libcrux_ml_dsa.Types.t_SigningError =
  let pre_hash_buffer:t_Array u8 (mk_usize 256) =
    Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 256)
  in
  let tmp0, out:(t_Array u8 (mk_usize 256) &
    Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (mk_usize 2420))
      Libcrux_ml_dsa.Types.t_SigningError) =
    Libcrux_ml_dsa.Ml_dsa_generic.Multiplexing.Ml_dsa_44_.sign_pre_hashed_shake128 (Libcrux_ml_dsa.Types.impl__as_ref
          (mk_usize 2560)
          signing_key
        <:
        t_Array u8 (mk_usize 2560))
      message
      context
      pre_hash_buffer
      randomness
  in
  let pre_hash_buffer:t_Array u8 (mk_usize 256) = tmp0 in
  out

/// Verify a HashML-DSA-44 Signature, with a SHAKE128 pre-hashing
/// The parameter `context` is used for domain separation
/// and is a byte string of length at most 255 bytes. It
/// may also be empty.
/// Returns `Ok` when the `signature` is valid for the `message` and
/// `verification_key`, and a [`VerificationError`] otherwise.
let verify_pre_hashed_shake128
      (verification_key: Libcrux_ml_dsa.Types.t_MLDSAVerificationKey (mk_usize 1312))
      (message context: t_Slice u8)
      (signature: Libcrux_ml_dsa.Types.t_MLDSASignature (mk_usize 2420))
    : Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError =
  let pre_hash_buffer:t_Array u8 (mk_usize 256) =
    Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 256)
  in
  let tmp0, out:(t_Array u8 (mk_usize 256) &
    Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError) =
    Libcrux_ml_dsa.Ml_dsa_generic.Multiplexing.Ml_dsa_44_.verify_pre_hashed_shake128 (Libcrux_ml_dsa.Types.impl_2__as_ref
          (mk_usize 1312)
          verification_key
        <:
        t_Array u8 (mk_usize 1312))
      message
      context
      pre_hash_buffer
      (Libcrux_ml_dsa.Types.impl_4__as_ref (mk_usize 2420) signature <: t_Array u8 (mk_usize 2420))
  in
  let pre_hash_buffer:t_Array u8 (mk_usize 256) = tmp0 in
  out
