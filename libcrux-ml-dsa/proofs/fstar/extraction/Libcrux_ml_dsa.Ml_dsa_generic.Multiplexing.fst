module Libcrux_ml_dsa.Ml_dsa_generic.Multiplexing
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let generate_key_pair
      (v_ROWS_IN_A v_COLUMNS_IN_A v_ETA v_ERROR_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE v_VERIFICATION_KEY_SIZE:
          usize)
      (randomness: t_Array u8 (sz 32))
     =
  if Libcrux_platform.Platform.simd256_support ()
  then
    Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Avx2.generate_key_pair v_ROWS_IN_A
      v_COLUMNS_IN_A
      v_ETA
      v_ERROR_RING_ELEMENT_SIZE
      v_SIGNING_KEY_SIZE
      v_VERIFICATION_KEY_SIZE
      randomness
  else
    if Libcrux_platform.Platform.simd128_support ()
    then
      Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.generate_key_pair v_ROWS_IN_A
        v_COLUMNS_IN_A
        v_ETA
        v_ERROR_RING_ELEMENT_SIZE
        v_SIGNING_KEY_SIZE
        v_VERIFICATION_KEY_SIZE
        randomness
    else
      Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.generate_key_pair v_ROWS_IN_A
        v_COLUMNS_IN_A
        v_ETA
        v_ERROR_RING_ELEMENT_SIZE
        v_SIGNING_KEY_SIZE
        v_VERIFICATION_KEY_SIZE
        randomness

let sign
      (v_ROWS_IN_A v_COLUMNS_IN_A v_ETA v_ERROR_RING_ELEMENT_SIZE v_GAMMA1_EXPONENT: usize)
      (v_GAMMA2: i32)
      (v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT v_GAMMA1_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE v_SIGNATURE_SIZE:
          usize)
      (signing_key: t_Array u8 v_SIGNING_KEY_SIZE)
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
     =
  if Libcrux_platform.Platform.simd256_support ()
  then
    Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Avx2.sign v_ROWS_IN_A v_COLUMNS_IN_A v_ETA
      v_ERROR_RING_ELEMENT_SIZE v_GAMMA1_EXPONENT v_GAMMA2 v_COMMITMENT_RING_ELEMENT_SIZE
      v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE
      v_MAX_ONES_IN_HINT v_GAMMA1_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE v_SIGNATURE_SIZE signing_key
      message context randomness
  else
    if Libcrux_platform.Platform.simd128_support ()
    then
      Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.sign v_ROWS_IN_A v_COLUMNS_IN_A v_ETA
        v_ERROR_RING_ELEMENT_SIZE v_GAMMA1_EXPONENT v_GAMMA2 v_COMMITMENT_RING_ELEMENT_SIZE
        v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE
        v_MAX_ONES_IN_HINT v_GAMMA1_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE v_SIGNATURE_SIZE
        signing_key message context randomness
    else
      Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.sign v_ROWS_IN_A v_COLUMNS_IN_A v_ETA
        v_ERROR_RING_ELEMENT_SIZE v_GAMMA1_EXPONENT v_GAMMA2 v_COMMITMENT_RING_ELEMENT_SIZE
        v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE
        v_MAX_ONES_IN_HINT v_GAMMA1_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE v_SIGNATURE_SIZE
        signing_key message context randomness

let sign_pre_hashed_shake128
      (v_ROWS_IN_A v_COLUMNS_IN_A v_ETA v_ERROR_RING_ELEMENT_SIZE v_GAMMA1_EXPONENT: usize)
      (v_GAMMA2: i32)
      (v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT v_GAMMA1_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE v_SIGNATURE_SIZE:
          usize)
      (signing_key: t_Array u8 v_SIGNING_KEY_SIZE)
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
     =
  if Libcrux_platform.Platform.simd256_support ()
  then
    Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Avx2.sign_pre_hashed_shake128 v_ROWS_IN_A
      v_COLUMNS_IN_A v_ETA v_ERROR_RING_ELEMENT_SIZE v_GAMMA1_EXPONENT v_GAMMA2
      v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE
      v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT v_GAMMA1_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE
      v_SIGNATURE_SIZE signing_key message context randomness
  else
    if Libcrux_platform.Platform.simd128_support ()
    then
      Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.sign_pre_hashed_shake128 v_ROWS_IN_A
        v_COLUMNS_IN_A v_ETA v_ERROR_RING_ELEMENT_SIZE v_GAMMA1_EXPONENT v_GAMMA2
        v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE
        v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT v_GAMMA1_RING_ELEMENT_SIZE
        v_SIGNING_KEY_SIZE v_SIGNATURE_SIZE signing_key message context randomness
    else
      Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.sign_pre_hashed_shake128 v_ROWS_IN_A
        v_COLUMNS_IN_A v_ETA v_ERROR_RING_ELEMENT_SIZE v_GAMMA1_EXPONENT v_GAMMA2
        v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE
        v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT v_GAMMA1_RING_ELEMENT_SIZE
        v_SIGNING_KEY_SIZE v_SIGNATURE_SIZE signing_key message context randomness

let verify
      (v_ROWS_IN_A v_COLUMNS_IN_A v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT v_GAMMA1_RING_ELEMENT_SIZE:
          usize)
      (v_GAMMA2 v_BETA: i32)
      (v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT:
          usize)
      (verification_key_serialized: t_Array u8 v_VERIFICATION_KEY_SIZE)
      (message context: t_Slice u8)
      (signature_serialized: t_Array u8 v_SIGNATURE_SIZE)
     =
  if Libcrux_platform.Platform.simd256_support ()
  then
    Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Avx2.verify v_ROWS_IN_A v_COLUMNS_IN_A
      v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT v_GAMMA1_RING_ELEMENT_SIZE v_GAMMA2
      v_BETA v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE
      v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT verification_key_serialized message context
      signature_serialized
  else
    if Libcrux_platform.Platform.simd128_support ()
    then
      Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.verify v_ROWS_IN_A v_COLUMNS_IN_A
        v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT v_GAMMA1_RING_ELEMENT_SIZE
        v_GAMMA2 v_BETA v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE
        v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT
        verification_key_serialized message context signature_serialized
    else
      Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.verify v_ROWS_IN_A v_COLUMNS_IN_A
        v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT v_GAMMA1_RING_ELEMENT_SIZE
        v_GAMMA2 v_BETA v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE
        v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT
        verification_key_serialized message context signature_serialized

let verify_pre_hashed_shake128
      (v_ROWS_IN_A v_COLUMNS_IN_A v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT v_GAMMA1_RING_ELEMENT_SIZE:
          usize)
      (v_GAMMA2 v_BETA: i32)
      (v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT:
          usize)
      (verification_key_serialized: t_Array u8 v_VERIFICATION_KEY_SIZE)
      (message context: t_Slice u8)
      (signature_serialized: t_Array u8 v_SIGNATURE_SIZE)
     =
  if Libcrux_platform.Platform.simd256_support ()
  then
    Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Avx2.verify_pre_hashed_shake128 v_ROWS_IN_A
      v_COLUMNS_IN_A v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT
      v_GAMMA1_RING_ELEMENT_SIZE v_GAMMA2 v_BETA v_COMMITMENT_RING_ELEMENT_SIZE
      v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE
      v_MAX_ONES_IN_HINT verification_key_serialized message context signature_serialized
  else
    if Libcrux_platform.Platform.simd128_support ()
    then
      Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.verify_pre_hashed_shake128 v_ROWS_IN_A
        v_COLUMNS_IN_A v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT
        v_GAMMA1_RING_ELEMENT_SIZE v_GAMMA2 v_BETA v_COMMITMENT_RING_ELEMENT_SIZE
        v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE
        v_MAX_ONES_IN_HINT verification_key_serialized message context signature_serialized
    else
      Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.verify_pre_hashed_shake128 v_ROWS_IN_A
        v_COLUMNS_IN_A v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT
        v_GAMMA1_RING_ELEMENT_SIZE v_GAMMA2 v_BETA v_COMMITMENT_RING_ELEMENT_SIZE
        v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE
        v_MAX_ONES_IN_HINT verification_key_serialized message context signature_serialized
