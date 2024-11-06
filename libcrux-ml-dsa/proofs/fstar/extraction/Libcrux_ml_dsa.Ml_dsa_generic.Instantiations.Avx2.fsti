module Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Avx2
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
  let open Libcrux_ml_dsa.Simd.Avx2 in
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

/// Generate key pair.
val generate_key_pair
      (v_ROWS_IN_A v_COLUMNS_IN_A v_ETA v_ERROR_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE v_VERIFICATION_KEY_SIZE:
          usize)
      (randomness: t_Array u8 (sz 32))
    : Prims.Pure (t_Array u8 v_SIGNING_KEY_SIZE & t_Array u8 v_VERIFICATION_KEY_SIZE)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Sign.
val sign
      (v_ROWS_IN_A v_COLUMNS_IN_A v_ETA v_ERROR_RING_ELEMENT_SIZE v_GAMMA1_EXPONENT: usize)
      (v_GAMMA2: i32)
      (v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT v_GAMMA1_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE v_SIGNATURE_SIZE:
          usize)
      (signing_key: t_Array u8 v_SIGNING_KEY_SIZE)
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
    : Prims.Pure
      (Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature v_SIGNATURE_SIZE)
          Libcrux_ml_dsa.Types.t_SigningError) Prims.l_True (fun _ -> Prims.l_True)

/// Sign (pre-hashed).
val sign_pre_hashed_shake128
      (v_ROWS_IN_A v_COLUMNS_IN_A v_ETA v_ERROR_RING_ELEMENT_SIZE v_GAMMA1_EXPONENT: usize)
      (v_GAMMA2: i32)
      (v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT v_GAMMA1_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE v_SIGNATURE_SIZE:
          usize)
      (signing_key: t_Array u8 v_SIGNING_KEY_SIZE)
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
    : Prims.Pure
      (Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature v_SIGNATURE_SIZE)
          Libcrux_ml_dsa.Types.t_SigningError) Prims.l_True (fun _ -> Prims.l_True)

/// Verify.
val verify
      (v_ROWS_IN_A v_COLUMNS_IN_A v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT v_GAMMA1_RING_ELEMENT_SIZE:
          usize)
      (v_GAMMA2 v_BETA: i32)
      (v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT:
          usize)
      (verification_key: t_Array u8 v_VERIFICATION_KEY_SIZE)
      (message context: t_Slice u8)
      (signature: t_Array u8 v_SIGNATURE_SIZE)
    : Prims.Pure (Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Verify (pre-hashed with SHAKE-128).
val verify_pre_hashed_shake128
      (v_ROWS_IN_A v_COLUMNS_IN_A v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT v_GAMMA1_RING_ELEMENT_SIZE:
          usize)
      (v_GAMMA2 v_BETA: i32)
      (v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT:
          usize)
      (verification_key: t_Array u8 v_VERIFICATION_KEY_SIZE)
      (message context: t_Slice u8)
      (signature: t_Array u8 v_SIGNATURE_SIZE)
    : Prims.Pure (Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError)
      Prims.l_True
      (fun _ -> Prims.l_True)
