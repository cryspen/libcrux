module Libcrux_ml_dsa.Ml_dsa_65_.Avx2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

/// Generate an ML-DSA-65 Key Pair
val generate_key_pair (randomness: t_Array u8 (sz 32))
    : Prims.Pure (Libcrux_ml_dsa.Types.t_MLDSAKeyPair (sz 1952) (sz 4032))
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Generate an ML-DSA-65 Key Pair
val generate_key_pair_mut
      (randomness: t_Array u8 (sz 32))
      (signing_key: t_Array u8 (sz 4032))
      (verification_key: t_Array u8 (sz 1952))
    : Prims.Pure (t_Array u8 (sz 4032) & t_Array u8 (sz 1952)) Prims.l_True (fun _ -> Prims.l_True)

/// Generate an ML-DSA-65 Signature
/// The parameter `context` is used for domain separation
/// and is a byte string of length at most 255 bytes. It
/// may also be empty.
val sign
      (signing_key: Libcrux_ml_dsa.Types.t_MLDSASigningKey (sz 4032))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
    : Prims.Pure
      (Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (sz 3309))
          Libcrux_ml_dsa.Types.t_SigningError) Prims.l_True (fun _ -> Prims.l_True)

/// Generate an ML-DSA-65 Signature
/// The parameter `context` is used for domain separation
/// and is a byte string of length at most 255 bytes. It
/// may also be empty.
val sign_mut
      (signing_key: t_Array u8 (sz 4032))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
      (signature: t_Array u8 (sz 3309))
    : Prims.Pure
      (t_Array u8 (sz 3309) & Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_SigningError)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Generate a HashML-DSA-65 Signature, with a SHAKE128 pre-hashing
/// The parameter `context` is used for domain separation
/// and is a byte string of length at most 255 bytes. It
/// may also be empty.
val sign_pre_hashed_shake128
      (signing_key: Libcrux_ml_dsa.Types.t_MLDSASigningKey (sz 4032))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
    : Prims.Pure
      (Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (sz 3309))
          Libcrux_ml_dsa.Types.t_SigningError) Prims.l_True (fun _ -> Prims.l_True)

/// Verify an ML-DSA-65 Signature
/// The parameter `context` is used for domain separation
/// and is a byte string of length at most 255 bytes. It
/// may also be empty.
val verify
      (verification_key: Libcrux_ml_dsa.Types.t_MLDSAVerificationKey (sz 1952))
      (message context: t_Slice u8)
      (signature: Libcrux_ml_dsa.Types.t_MLDSASignature (sz 3309))
    : Prims.Pure (Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Verify a HashML-DSA-65 Signature, with a SHAKE128 pre-hashing
/// The parameter `context` is used for domain separation
/// and is a byte string of length at most 255 bytes. It
/// may also be empty.
val verify_pre_hashed_shake128
      (verification_key: Libcrux_ml_dsa.Types.t_MLDSAVerificationKey (sz 1952))
      (message context: t_Slice u8)
      (signature: Libcrux_ml_dsa.Types.t_MLDSASignature (sz 3309))
    : Prims.Pure (Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError)
      Prims.l_True
      (fun _ -> Prims.l_True)
