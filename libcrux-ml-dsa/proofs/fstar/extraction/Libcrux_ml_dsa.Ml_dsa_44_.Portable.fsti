module Libcrux_ml_dsa.Ml_dsa_44_.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

/// Generate an ML-DSA-44 Signature
val sign
      (signing_key: Libcrux_ml_dsa.Types.t_MLDSASigningKey (sz 2560))
      (message: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
    : Prims.Pure
      (Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (sz 2420))
          Libcrux_ml_dsa.Ml_dsa_generic.t_SigningError) Prims.l_True (fun _ -> Prims.l_True)

/// Verify an ML-DSA-44 Signature
val verify
      (verification_key: Libcrux_ml_dsa.Types.t_MLDSAVerificationKey (sz 1312))
      (message: t_Slice u8)
      (signature: Libcrux_ml_dsa.Types.t_MLDSASignature (sz 2420))
    : Prims.Pure (Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Ml_dsa_generic.t_VerificationError)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Generate an ML-DSA-44 Key Pair
val generate_key_pair (randomness: t_Array u8 (sz 32))
    : Prims.Pure (Libcrux_ml_dsa.Types.t_MLDSAKeyPair (sz 1312) (sz 2560))
      Prims.l_True
      (fun _ -> Prims.l_True)
