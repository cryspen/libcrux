module Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Avx2.Ml_dsa_44_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Hash_functions.Portable in
  let open Libcrux_ml_dsa.Hash_functions.Shake128 in
  let open Libcrux_ml_dsa.Hash_functions.Shake256 in
  let open Libcrux_ml_dsa.Hash_functions.Simd256 in
  let open Libcrux_ml_dsa.Pre_hash in
  let open Libcrux_ml_dsa.Samplex4 in
  let open Libcrux_ml_dsa.Samplex4.Avx2 in
  let open Libcrux_ml_dsa.Simd.Avx2 in
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

/// Key Generation.
val generate_key_pair___inner
      (randomness: t_Array u8 (sz 32))
      (signing_key verification_key: t_Slice u8)
    : Prims.Pure (t_Slice u8 & t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

val generate_key_pair (randomness: t_Array u8 (sz 32)) (signing_key verification_key: t_Slice u8)
    : Prims.Pure (t_Slice u8 & t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

val sign___inner
      (signing_key: t_Array u8 (sz 2560))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
    : Prims.Pure
      (Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (sz 2420))
          Libcrux_ml_dsa.Types.t_SigningError) Prims.l_True (fun _ -> Prims.l_True)

/// Sign.
val sign
      (signing_key: t_Array u8 (sz 2560))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
    : Prims.Pure
      (Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (sz 2420))
          Libcrux_ml_dsa.Types.t_SigningError) Prims.l_True (fun _ -> Prims.l_True)

val sign_mut___inner
      (signing_key: t_Array u8 (sz 2560))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
      (signature: t_Array u8 (sz 2420))
    : Prims.Pure
      (t_Array u8 (sz 2420) & Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_SigningError)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Sign.
val sign_mut
      (signing_key: t_Array u8 (sz 2560))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
      (signature: t_Array u8 (sz 2420))
    : Prims.Pure
      (t_Array u8 (sz 2420) & Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_SigningError)
      Prims.l_True
      (fun _ -> Prims.l_True)

val sign_pre_hashed_shake128___inner
      (signing_key: t_Array u8 (sz 2560))
      (message context pre_hash_buffer: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
    : Prims.Pure
      (t_Slice u8 &
        Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (sz 2420))
          Libcrux_ml_dsa.Types.t_SigningError) Prims.l_True (fun _ -> Prims.l_True)

/// Sign (pre-hashed).
val sign_pre_hashed_shake128
      (signing_key: t_Array u8 (sz 2560))
      (message context pre_hash_buffer: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
    : Prims.Pure
      (t_Slice u8 &
        Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (sz 2420))
          Libcrux_ml_dsa.Types.t_SigningError) Prims.l_True (fun _ -> Prims.l_True)

val verify___inner
      (verification_key: t_Array u8 (sz 1312))
      (message context: t_Slice u8)
      (signature: t_Array u8 (sz 2420))
    : Prims.Pure (Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Verify.
val verify
      (verification_key: t_Array u8 (sz 1312))
      (message context: t_Slice u8)
      (signature: t_Array u8 (sz 2420))
    : Prims.Pure (Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError)
      Prims.l_True
      (fun _ -> Prims.l_True)

val verify_pre_hashed_shake128___inner
      (verification_key: t_Array u8 (sz 1312))
      (message context pre_hash_buffer: t_Slice u8)
      (signature: t_Array u8 (sz 2420))
    : Prims.Pure
      (t_Slice u8 & Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Verify (pre-hashed with SHAKE-128).
val verify_pre_hashed_shake128
      (verification_key: t_Array u8 (sz 1312))
      (message context pre_hash_buffer: t_Slice u8)
      (signature: t_Array u8 (sz 2420))
    : Prims.Pure
      (t_Slice u8 & Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError)
      Prims.l_True
      (fun _ -> Prims.l_True)
