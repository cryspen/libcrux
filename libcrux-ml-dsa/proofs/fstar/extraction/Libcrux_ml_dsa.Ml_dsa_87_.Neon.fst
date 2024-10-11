module Libcrux_ml_dsa.Ml_dsa_87_.Neon
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// Generate an ML-DSA-87 Signature
/// The parameter `context` is used for domain separation
/// and is a byte string of length at most 255 bytes. It
/// may also be empty.
let sign
      (signing_key: Libcrux_ml_dsa.Types.t_MLDSASigningKey (Rust_primitives.mk_usize 4896))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (Rust_primitives.mk_usize 32))
    : Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (Rust_primitives.mk_usize 4627))
      Libcrux_ml_dsa.Ml_dsa_generic.t_SigningError =
  Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.sign (Rust_primitives.mk_usize 8)
    (Rust_primitives.mk_usize 7) (Rust_primitives.mk_usize 2) (Rust_primitives.mk_usize 96)
    (Rust_primitives.mk_usize 19) (Rust_primitives.mk_i32 261888) (Rust_primitives.mk_usize 128)
    (Rust_primitives.mk_usize 1024) (Rust_primitives.mk_usize 64) (Rust_primitives.mk_usize 60)
    (Rust_primitives.mk_usize 75) (Rust_primitives.mk_usize 640) (Rust_primitives.mk_usize 4896)
    (Rust_primitives.mk_usize 4627) signing_key.Libcrux_ml_dsa.Types._0 message context randomness

/// Generate a HashML-DSA-87 Signature, with a SHAKE128 pre-hashing
/// The parameter `context` is used for domain separation
/// and is a byte string of length at most 255 bytes. It
/// may also be empty.
let sign_pre_hashed_shake128
      (signing_key: Libcrux_ml_dsa.Types.t_MLDSASigningKey (Rust_primitives.mk_usize 4896))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (Rust_primitives.mk_usize 32))
    : Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (Rust_primitives.mk_usize 4627))
      Libcrux_ml_dsa.Ml_dsa_generic.t_SigningError =
  Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.sign_pre_hashed_shake128 (Rust_primitives.mk_usize
      8) (Rust_primitives.mk_usize 7) (Rust_primitives.mk_usize 2) (Rust_primitives.mk_usize 96)
    (Rust_primitives.mk_usize 19) (Rust_primitives.mk_i32 261888) (Rust_primitives.mk_usize 128)
    (Rust_primitives.mk_usize 1024) (Rust_primitives.mk_usize 64) (Rust_primitives.mk_usize 60)
    (Rust_primitives.mk_usize 75) (Rust_primitives.mk_usize 640) (Rust_primitives.mk_usize 4896)
    (Rust_primitives.mk_usize 4627) signing_key.Libcrux_ml_dsa.Types._0 message context randomness

/// Verify an ML-DSA-87 Signature
/// The parameter `context` is used for domain separation
/// and is a byte string of length at most 255 bytes. It
/// may also be empty.
let verify
      (verification_key:
          Libcrux_ml_dsa.Types.t_MLDSAVerificationKey (Rust_primitives.mk_usize 2592))
      (message context: t_Slice u8)
      (signature: Libcrux_ml_dsa.Types.t_MLDSASignature (Rust_primitives.mk_usize 4627))
    : Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Ml_dsa_generic.t_VerificationError =
  Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.verify (Rust_primitives.mk_usize 8)
    (Rust_primitives.mk_usize 7) (Rust_primitives.mk_usize 4627) (Rust_primitives.mk_usize 2592)
    (Rust_primitives.mk_usize 19) (Rust_primitives.mk_usize 640) (Rust_primitives.mk_i32 261888)
    (Rust_primitives.mk_i32 120) (Rust_primitives.mk_usize 128) (Rust_primitives.mk_usize 1024)
    (Rust_primitives.mk_usize 64) (Rust_primitives.mk_usize 60) (Rust_primitives.mk_usize 75)
    verification_key.Libcrux_ml_dsa.Types._0 message context signature.Libcrux_ml_dsa.Types._0

/// Verify a HashML-DSA-87 Signature, with a SHAKE128 pre-hashing
/// The parameter `context` is used for domain separation
/// and is a byte string of length at most 255 bytes. It
/// may also be empty.
let verify_pre_hashed_shake128
      (verification_key:
          Libcrux_ml_dsa.Types.t_MLDSAVerificationKey (Rust_primitives.mk_usize 2592))
      (message context: t_Slice u8)
      (signature: Libcrux_ml_dsa.Types.t_MLDSASignature (Rust_primitives.mk_usize 4627))
    : Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Ml_dsa_generic.t_VerificationError =
  Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.verify_pre_hashed_shake128 (Rust_primitives.mk_usize
      8) (Rust_primitives.mk_usize 7) (Rust_primitives.mk_usize 4627)
    (Rust_primitives.mk_usize 2592) (Rust_primitives.mk_usize 19) (Rust_primitives.mk_usize 640)
    (Rust_primitives.mk_i32 261888) (Rust_primitives.mk_i32 120) (Rust_primitives.mk_usize 128)
    (Rust_primitives.mk_usize 1024) (Rust_primitives.mk_usize 64) (Rust_primitives.mk_usize 60)
    (Rust_primitives.mk_usize 75) verification_key.Libcrux_ml_dsa.Types._0 message context
    signature.Libcrux_ml_dsa.Types._0

/// Generate an ML-DSA-87 Key Pair
let generate_key_pair (randomness: t_Array u8 (Rust_primitives.mk_usize 32))
    : Libcrux_ml_dsa.Types.t_MLDSAKeyPair (Rust_primitives.mk_usize 2592)
      (Rust_primitives.mk_usize 4896) =
  let signing_key, verification_key:(t_Array u8 (Rust_primitives.mk_usize 4896) &
    t_Array u8 (Rust_primitives.mk_usize 2592)) =
    Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.generate_key_pair (Rust_primitives.mk_usize 8)
      (Rust_primitives.mk_usize 7)
      (Rust_primitives.mk_usize 2)
      (Rust_primitives.mk_usize 96)
      (Rust_primitives.mk_usize 4896)
      (Rust_primitives.mk_usize 2592)
      randomness
  in
  {
    Libcrux_ml_dsa.Types.f_signing_key
    =
    Libcrux_ml_dsa.Types.MLDSASigningKey signing_key
    <:
    Libcrux_ml_dsa.Types.t_MLDSASigningKey (Rust_primitives.mk_usize 4896);
    Libcrux_ml_dsa.Types.f_verification_key
    =
    Libcrux_ml_dsa.Types.MLDSAVerificationKey verification_key
    <:
    Libcrux_ml_dsa.Types.t_MLDSAVerificationKey (Rust_primitives.mk_usize 2592)
  }
  <:
  Libcrux_ml_dsa.Types.t_MLDSAKeyPair (Rust_primitives.mk_usize 2592)
    (Rust_primitives.mk_usize 4896)
