module Libcrux_ml_dsa.Ml_dsa_generic.Multiplexing.Ml_dsa_44_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

val generate_key_pair
      (randomness: t_Array u8 (mk_usize 32))
      (signing_key: t_Array u8 (mk_usize 2560))
      (verification_key: t_Array u8 (mk_usize 1312))
    : Prims.Pure (t_Array u8 (mk_usize 2560) & t_Array u8 (mk_usize 1312))
      Prims.l_True
      (fun _ -> Prims.l_True)

val sign
      (signing_key: t_Array u8 (mk_usize 2560))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (mk_usize 32))
    : Prims.Pure
      (Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (mk_usize 2420))
          Libcrux_ml_dsa.Types.t_SigningError) Prims.l_True (fun _ -> Prims.l_True)

val sign_pre_hashed_shake128
      (signing_key: t_Array u8 (mk_usize 2560))
      (message context pre_hash_buffer: t_Slice u8)
      (randomness: t_Array u8 (mk_usize 32))
    : Prims.Pure
      (t_Slice u8 &
        Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (mk_usize 2420))
          Libcrux_ml_dsa.Types.t_SigningError) Prims.l_True (fun _ -> Prims.l_True)

val verify
      (verification_key_serialized: t_Array u8 (mk_usize 1312))
      (message context: t_Slice u8)
      (signature_serialized: t_Array u8 (mk_usize 2420))
    : Prims.Pure (Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError)
      Prims.l_True
      (fun _ -> Prims.l_True)

val verify_pre_hashed_shake128
      (verification_key_serialized: t_Array u8 (mk_usize 1312))
      (message context pre_hash_buffer: t_Slice u8)
      (signature_serialized: t_Array u8 (mk_usize 2420))
    : Prims.Pure
      (t_Slice u8 & Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError)
      Prims.l_True
      (fun _ -> Prims.l_True)
