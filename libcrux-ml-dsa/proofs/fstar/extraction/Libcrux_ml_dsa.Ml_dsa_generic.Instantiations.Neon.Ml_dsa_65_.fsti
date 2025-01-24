module Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.Ml_dsa_65_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Hash_functions.Neon in
  let open Libcrux_ml_dsa.Hash_functions.Portable in
  let open Libcrux_ml_dsa.Hash_functions.Shake128 in
  let open Libcrux_ml_dsa.Hash_functions.Shake256 in
  let open Libcrux_ml_dsa.Pre_hash in
  let open Libcrux_ml_dsa.Samplex4 in
  let open Libcrux_ml_dsa.Samplex4.Neon in
  let open Libcrux_ml_dsa.Simd.Portable in
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

/// Generate key pair.
val generate_key_pair
      (randomness: t_Array u8 (sz 32))
      (signing_key: t_Array u8 (sz 4032))
      (verification_key: t_Array u8 (sz 1952))
    : Prims.Pure (t_Array u8 (sz 4032) & t_Array u8 (sz 1952)) Prims.l_True (fun _ -> Prims.l_True)

/// Sign.
val sign
      (signing_key: t_Array u8 (sz 4032))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
    : Prims.Pure
      (Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (sz 3309))
          Libcrux_ml_dsa.Types.t_SigningError) Prims.l_True (fun _ -> Prims.l_True)

/// Sign.
val sign_mut
      (signing_key: t_Array u8 (sz 4032))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
      (signature: t_Array u8 (sz 3309))
    : Prims.Pure
      (t_Array u8 (sz 3309) & Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_SigningError)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Sign (pre-hashed).
val sign_pre_hashed_shake128
      (signing_key: t_Array u8 (sz 4032))
      (message context pre_hash_buffer: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
    : Prims.Pure
      (t_Slice u8 &
        Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (sz 3309))
          Libcrux_ml_dsa.Types.t_SigningError) Prims.l_True (fun _ -> Prims.l_True)

/// Verify.
val verify
      (verification_key: t_Array u8 (sz 1952))
      (message context: t_Slice u8)
      (signature: t_Array u8 (sz 3309))
    : Prims.Pure (Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Verify (pre-hashed with SHAKE-128).
val verify_pre_hashed_shake128
      (verification_key: t_Array u8 (sz 1952))
      (message context pre_hash_buffer: t_Slice u8)
      (signature: t_Array u8 (sz 3309))
    : Prims.Pure
      (t_Slice u8 & Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError)
      Prims.l_True
      (fun _ -> Prims.l_True)
