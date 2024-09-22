module Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Hash_functions.Neon in
  let open Libcrux_ml_dsa.Hash_functions.Portable in
  let open Libcrux_ml_dsa.Simd.Portable in
  ()

let generate_key_pair
      (v_ROWS_IN_A v_COLUMNS_IN_A v_ETA v_ERROR_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE v_VERIFICATION_KEY_SIZE:
          usize)
      (randomness: t_Array u8 (sz 32))
     =
  Libcrux_ml_dsa.Ml_dsa_generic.generate_key_pair #Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
    #Libcrux_ml_dsa.Hash_functions.Neon.t_Shake128x4
    #Libcrux_ml_dsa.Hash_functions.Portable.t_Shake256
    #Libcrux_ml_dsa.Hash_functions.Neon.t_Shake256x4 v_ROWS_IN_A v_COLUMNS_IN_A v_ETA
    v_ERROR_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE v_VERIFICATION_KEY_SIZE randomness

let sign
      (v_ROWS_IN_A v_COLUMNS_IN_A v_ETA v_ERROR_RING_ELEMENT_SIZE v_GAMMA1_EXPONENT: usize)
      (v_GAMMA2: i32)
      (v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT v_GAMMA1_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE v_SIGNATURE_SIZE:
          usize)
      (signing_key: t_Array u8 v_SIGNING_KEY_SIZE)
      (message: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
     =
  Libcrux_ml_dsa.Ml_dsa_generic.sign #Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
    #Libcrux_ml_dsa.Hash_functions.Neon.t_Shake128x4
    #Libcrux_ml_dsa.Hash_functions.Portable.t_Shake256
    #Libcrux_ml_dsa.Hash_functions.Neon.t_Shake256x4 v_ROWS_IN_A v_COLUMNS_IN_A v_ETA
    v_ERROR_RING_ELEMENT_SIZE v_GAMMA1_EXPONENT v_GAMMA2 v_COMMITMENT_RING_ELEMENT_SIZE
    v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT
    v_GAMMA1_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE v_SIGNATURE_SIZE signing_key message randomness

let verify
      (v_ROWS_IN_A v_COLUMNS_IN_A v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT v_GAMMA1_RING_ELEMENT_SIZE:
          usize)
      (v_GAMMA2 v_BETA: i32)
      (v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT:
          usize)
      (verification_key: t_Array u8 v_VERIFICATION_KEY_SIZE)
      (message: t_Slice u8)
      (signature: t_Array u8 v_SIGNATURE_SIZE)
     =
  Libcrux_ml_dsa.Ml_dsa_generic.verify #Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
    #Libcrux_ml_dsa.Hash_functions.Neon.t_Shake128x4
    #Libcrux_ml_dsa.Hash_functions.Portable.t_Shake256 v_ROWS_IN_A v_COLUMNS_IN_A v_SIGNATURE_SIZE
    v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT v_GAMMA1_RING_ELEMENT_SIZE v_GAMMA2 v_BETA
    v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE
    v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT verification_key message signature
