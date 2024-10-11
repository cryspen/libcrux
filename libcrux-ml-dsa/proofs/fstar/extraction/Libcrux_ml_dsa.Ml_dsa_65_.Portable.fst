module Libcrux_ml_dsa.Ml_dsa_65_.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// Generate an ML-DSA-65 Signature
/// The parameter `context` is used for domain separation
/// and is a byte string of length at most 255 bytes. It
/// may also be empty.
let sign
      (signing_key: Libcrux_ml_dsa.Types.t_MLDSASigningKey (Rust_primitives.mk_usize 4032))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (Rust_primitives.mk_usize 32))
    : Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (Rust_primitives.mk_usize 3309))
      Libcrux_ml_dsa.Ml_dsa_generic.t_SigningError =
  Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.sign (Rust_primitives.mk_usize 6)
    (Rust_primitives.mk_usize 5) (Rust_primitives.mk_usize 4) (Rust_primitives.mk_usize 128)
    (Rust_primitives.mk_usize 19) (Rust_primitives.mk_i32 261888) (Rust_primitives.mk_usize 128)
    (Rust_primitives.mk_usize 768) (Rust_primitives.mk_usize 48) (Rust_primitives.mk_usize 49)
    (Rust_primitives.mk_usize 55) (Rust_primitives.mk_usize 640) (Rust_primitives.mk_usize 4032)
    (Rust_primitives.mk_usize 3309) signing_key.Libcrux_ml_dsa.Types._0 message context randomness

/// Generate a HashML-DSA-65 Signature, with a SHAKE128 pre-hashing
/// The parameter `context` is used for domain separation
/// and is a byte string of length at most 255 bytes. It
/// may also be empty.
let sign_pre_hashed_shake128
      (signing_key: Libcrux_ml_dsa.Types.t_MLDSASigningKey (Rust_primitives.mk_usize 4032))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (Rust_primitives.mk_usize 32))
    : Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (Rust_primitives.mk_usize 3309))
      Libcrux_ml_dsa.Ml_dsa_generic.t_SigningError =
  Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.sign_pre_hashed_shake128 (Rust_primitives.mk_usize
      6) (Rust_primitives.mk_usize 5) (Rust_primitives.mk_usize 4) (Rust_primitives.mk_usize 128)
    (Rust_primitives.mk_usize 19) (Rust_primitives.mk_i32 261888) (Rust_primitives.mk_usize 128)
    (Rust_primitives.mk_usize 768) (Rust_primitives.mk_usize 48) (Rust_primitives.mk_usize 49)
    (Rust_primitives.mk_usize 55) (Rust_primitives.mk_usize 640) (Rust_primitives.mk_usize 4032)
    (Rust_primitives.mk_usize 3309) signing_key.Libcrux_ml_dsa.Types._0 message context randomness

/// Verify an ML-DSA-65 Signature
/// The parameter `context` is used for domain separation
/// and is a byte string of length at most 255 bytes. It
/// may also be empty.
let verify
      (verification_key:
          Libcrux_ml_dsa.Types.t_MLDSAVerificationKey (Rust_primitives.mk_usize 1952))
      (message context: t_Slice u8)
      (signature: Libcrux_ml_dsa.Types.t_MLDSASignature (Rust_primitives.mk_usize 3309))
    : Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Ml_dsa_generic.t_VerificationError =
  Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.verify (Rust_primitives.mk_usize 6)
    (Rust_primitives.mk_usize 5) (Rust_primitives.mk_usize 3309) (Rust_primitives.mk_usize 1952)
    (Rust_primitives.mk_usize 19) (Rust_primitives.mk_usize 640) (Rust_primitives.mk_i32 261888)
    (Rust_primitives.mk_i32 196) (Rust_primitives.mk_usize 128) (Rust_primitives.mk_usize 768)
    (Rust_primitives.mk_usize 48) (Rust_primitives.mk_usize 49) (Rust_primitives.mk_usize 55)
    verification_key.Libcrux_ml_dsa.Types._0 message context signature.Libcrux_ml_dsa.Types._0

/// Verify a HashML-DSA-65 Signature, with a SHAKE128 pre-hashing
/// The parameter `context` is used for domain separation
/// and is a byte string of length at most 255 bytes. It
/// may also be empty.
let verify_pre_hashed_shake128
      (verification_key:
          Libcrux_ml_dsa.Types.t_MLDSAVerificationKey (Rust_primitives.mk_usize 1952))
      (message context: t_Slice u8)
      (signature: Libcrux_ml_dsa.Types.t_MLDSASignature (Rust_primitives.mk_usize 3309))
    : Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Ml_dsa_generic.t_VerificationError =
  Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.verify_pre_hashed_shake128 (Rust_primitives.mk_usize
      6) (Rust_primitives.mk_usize 5) (Rust_primitives.mk_usize 3309)
    (Rust_primitives.mk_usize 1952) (Rust_primitives.mk_usize 19) (Rust_primitives.mk_usize 640)
    (Rust_primitives.mk_i32 261888) (Rust_primitives.mk_i32 196) (Rust_primitives.mk_usize 128)
    (Rust_primitives.mk_usize 768) (Rust_primitives.mk_usize 48) (Rust_primitives.mk_usize 49)
    (Rust_primitives.mk_usize 55) verification_key.Libcrux_ml_dsa.Types._0 message context
    signature.Libcrux_ml_dsa.Types._0

/// Generate an ML-DSA-65 Key Pair
let generate_key_pair (randomness: t_Array u8 (Rust_primitives.mk_usize 32))
    : Libcrux_ml_dsa.Types.t_MLDSAKeyPair (Rust_primitives.mk_usize 1952)
      (Rust_primitives.mk_usize 4032) =
  let signing_key, verification_key:(t_Array u8 (Rust_primitives.mk_usize 4032) &
    t_Array u8 (Rust_primitives.mk_usize 1952)) =
    Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.generate_key_pair (Rust_primitives.mk_usize
        6)
      (Rust_primitives.mk_usize 5)
      (Rust_primitives.mk_usize 4)
      (Rust_primitives.mk_usize 128)
      (Rust_primitives.mk_usize 4032)
      (Rust_primitives.mk_usize 1952)
      randomness
  in
  {
    Libcrux_ml_dsa.Types.f_signing_key
    =
    Libcrux_ml_dsa.Types.MLDSASigningKey signing_key
    <:
    Libcrux_ml_dsa.Types.t_MLDSASigningKey (Rust_primitives.mk_usize 4032);
    Libcrux_ml_dsa.Types.f_verification_key
    =
    Libcrux_ml_dsa.Types.MLDSAVerificationKey verification_key
    <:
    Libcrux_ml_dsa.Types.t_MLDSAVerificationKey (Rust_primitives.mk_usize 1952)
  }
  <:
  Libcrux_ml_dsa.Types.t_MLDSAKeyPair (Rust_primitives.mk_usize 1952)
    (Rust_primitives.mk_usize 4032)
