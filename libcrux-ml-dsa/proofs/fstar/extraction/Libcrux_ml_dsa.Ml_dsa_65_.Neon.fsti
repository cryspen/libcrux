module Libcrux_ml_dsa.Ml_dsa_65_.Neon
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

/// Generate an ML-DSA-65 Signature
val sign
      (signing_key: Libcrux_ml_dsa.Types.t_MLDSASigningKey (Rust_primitives.mk_usize 4032))
      (message: t_Slice u8)
      (randomness: t_Array u8 (Rust_primitives.mk_usize 32))
    : Prims.Pure
      (Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (Rust_primitives.mk_usize 3309))
          Libcrux_ml_dsa.Ml_dsa_generic.t_SigningError) Prims.l_True (fun _ -> Prims.l_True)

/// Verify an ML-DSA-65 Signature
val verify
      (verification_key: Libcrux_ml_dsa.Types.t_MLDSAVerificationKey (Rust_primitives.mk_usize 1952)
        )
      (message: t_Slice u8)
      (signature: Libcrux_ml_dsa.Types.t_MLDSASignature (Rust_primitives.mk_usize 3309))
    : Prims.Pure (Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Ml_dsa_generic.t_VerificationError)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Generate an ML-DSA-65 Key Pair
val generate_key_pair (randomness: t_Array u8 (Rust_primitives.mk_usize 32))
    : Prims.Pure
      (Libcrux_ml_dsa.Types.t_MLDSAKeyPair (Rust_primitives.mk_usize 1952)
          (Rust_primitives.mk_usize 4032)) Prims.l_True (fun _ -> Prims.l_True)
