module Libcrux_ml_dsa.Ml_dsa_generic.Multiplexing
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let generate_key_pair_v44
      (randomness: t_Array u8 (sz 32))
      (signing_key verification_key: t_Slice u8)
     =
  let (signing_key, verification_key), hax_temp_output:((t_Slice u8 & t_Slice u8) & Prims.unit) =
    if Libcrux_platform.Platform.simd256_support ()
    then
      let tmp0, tmp1:(t_Slice u8 & t_Slice u8) =
        Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.generate_key_pair_v44 randomness
          signing_key
          verification_key
      in
      let signing_key:t_Slice u8 = tmp0 in
      let verification_key:t_Slice u8 = tmp1 in
      let _:Prims.unit = () in
      (signing_key, verification_key <: (t_Slice u8 & t_Slice u8)), ()
      <:
      ((t_Slice u8 & t_Slice u8) & Prims.unit)
    else
      if Libcrux_platform.Platform.simd128_support ()
      then
        let tmp0, tmp1:(t_Slice u8 & t_Slice u8) =
          Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.generate_key_pair_v44 randomness
            signing_key
            verification_key
        in
        let signing_key:t_Slice u8 = tmp0 in
        let verification_key:t_Slice u8 = tmp1 in
        let _:Prims.unit = () in
        (signing_key, verification_key <: (t_Slice u8 & t_Slice u8)), ()
        <:
        ((t_Slice u8 & t_Slice u8) & Prims.unit)
      else
        let tmp0, tmp1:(t_Slice u8 & t_Slice u8) =
          Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.generate_key_pair_v44 randomness
            signing_key
            verification_key
        in
        let signing_key:t_Slice u8 = tmp0 in
        let verification_key:t_Slice u8 = tmp1 in
        let _:Prims.unit = () in
        (signing_key, verification_key <: (t_Slice u8 & t_Slice u8)), ()
        <:
        ((t_Slice u8 & t_Slice u8) & Prims.unit)
  in
  signing_key, verification_key <: (t_Slice u8 & t_Slice u8)

let generate_key_pair_v65
      (randomness: t_Array u8 (sz 32))
      (signing_key verification_key: t_Slice u8)
     =
  let (signing_key, verification_key), hax_temp_output:((t_Slice u8 & t_Slice u8) & Prims.unit) =
    if Libcrux_platform.Platform.simd256_support ()
    then
      let tmp0, tmp1:(t_Slice u8 & t_Slice u8) =
        Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.generate_key_pair_v65 randomness
          signing_key
          verification_key
      in
      let signing_key:t_Slice u8 = tmp0 in
      let verification_key:t_Slice u8 = tmp1 in
      let _:Prims.unit = () in
      (signing_key, verification_key <: (t_Slice u8 & t_Slice u8)), ()
      <:
      ((t_Slice u8 & t_Slice u8) & Prims.unit)
    else
      if Libcrux_platform.Platform.simd128_support ()
      then
        let tmp0, tmp1:(t_Slice u8 & t_Slice u8) =
          Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.generate_key_pair_v65 randomness
            signing_key
            verification_key
        in
        let signing_key:t_Slice u8 = tmp0 in
        let verification_key:t_Slice u8 = tmp1 in
        let _:Prims.unit = () in
        (signing_key, verification_key <: (t_Slice u8 & t_Slice u8)), ()
        <:
        ((t_Slice u8 & t_Slice u8) & Prims.unit)
      else
        let tmp0, tmp1:(t_Slice u8 & t_Slice u8) =
          Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.generate_key_pair_v65 randomness
            signing_key
            verification_key
        in
        let signing_key:t_Slice u8 = tmp0 in
        let verification_key:t_Slice u8 = tmp1 in
        let _:Prims.unit = () in
        (signing_key, verification_key <: (t_Slice u8 & t_Slice u8)), ()
        <:
        ((t_Slice u8 & t_Slice u8) & Prims.unit)
  in
  signing_key, verification_key <: (t_Slice u8 & t_Slice u8)

let generate_key_pair_v87
      (randomness: t_Array u8 (sz 32))
      (signing_key verification_key: t_Slice u8)
     =
  let (signing_key, verification_key), hax_temp_output:((t_Slice u8 & t_Slice u8) & Prims.unit) =
    if Libcrux_platform.Platform.simd256_support ()
    then
      let tmp0, tmp1:(t_Slice u8 & t_Slice u8) =
        Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.generate_key_pair_v87 randomness
          signing_key
          verification_key
      in
      let signing_key:t_Slice u8 = tmp0 in
      let verification_key:t_Slice u8 = tmp1 in
      let _:Prims.unit = () in
      (signing_key, verification_key <: (t_Slice u8 & t_Slice u8)), ()
      <:
      ((t_Slice u8 & t_Slice u8) & Prims.unit)
    else
      if Libcrux_platform.Platform.simd128_support ()
      then
        let tmp0, tmp1:(t_Slice u8 & t_Slice u8) =
          Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.generate_key_pair_v87 randomness
            signing_key
            verification_key
        in
        let signing_key:t_Slice u8 = tmp0 in
        let verification_key:t_Slice u8 = tmp1 in
        let _:Prims.unit = () in
        (signing_key, verification_key <: (t_Slice u8 & t_Slice u8)), ()
        <:
        ((t_Slice u8 & t_Slice u8) & Prims.unit)
      else
        let tmp0, tmp1:(t_Slice u8 & t_Slice u8) =
          Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.generate_key_pair_v87 randomness
            signing_key
            verification_key
        in
        let signing_key:t_Slice u8 = tmp0 in
        let verification_key:t_Slice u8 = tmp1 in
        let _:Prims.unit = () in
        (signing_key, verification_key <: (t_Slice u8 & t_Slice u8)), ()
        <:
        ((t_Slice u8 & t_Slice u8) & Prims.unit)
  in
  signing_key, verification_key <: (t_Slice u8 & t_Slice u8)

let sign
      (v_ROWS_IN_A v_COLUMNS_IN_A v_ROWS_X_COLUMNS v_ETA v_ERROR_RING_ELEMENT_SIZE v_GAMMA1_EXPONENT:
          usize)
      (v_GAMMA2: i32)
      (v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT v_GAMMA1_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE v_SIGNATURE_SIZE:
          usize)
      (signing_key: t_Array u8 v_SIGNING_KEY_SIZE)
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
     =
  if Libcrux_platform.Platform.simd256_support ()
  then
    Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Avx2.sign v_ROWS_IN_A v_COLUMNS_IN_A
      v_ROWS_X_COLUMNS v_ETA v_ERROR_RING_ELEMENT_SIZE v_GAMMA1_EXPONENT v_GAMMA2
      v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE
      v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT v_GAMMA1_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE
      v_SIGNATURE_SIZE signing_key message context randomness
  else
    if Libcrux_platform.Platform.simd128_support ()
    then
      Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.sign v_ROWS_IN_A v_COLUMNS_IN_A
        v_ROWS_X_COLUMNS v_ETA v_ERROR_RING_ELEMENT_SIZE v_GAMMA1_EXPONENT v_GAMMA2
        v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE
        v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT v_GAMMA1_RING_ELEMENT_SIZE
        v_SIGNING_KEY_SIZE v_SIGNATURE_SIZE signing_key message context randomness
    else
      Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.sign v_ROWS_IN_A v_COLUMNS_IN_A
        v_ROWS_X_COLUMNS v_ETA v_ERROR_RING_ELEMENT_SIZE v_GAMMA1_EXPONENT v_GAMMA2
        v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE
        v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT v_GAMMA1_RING_ELEMENT_SIZE
        v_SIGNING_KEY_SIZE v_SIGNATURE_SIZE signing_key message context randomness

let sign_pre_hashed_shake128
      (v_ROWS_IN_A v_COLUMNS_IN_A v_ROWS_X_COLUMNS v_ETA v_ERROR_RING_ELEMENT_SIZE v_GAMMA1_EXPONENT:
          usize)
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
      v_COLUMNS_IN_A v_ROWS_X_COLUMNS v_ETA v_ERROR_RING_ELEMENT_SIZE v_GAMMA1_EXPONENT v_GAMMA2
      v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE
      v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT v_GAMMA1_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE
      v_SIGNATURE_SIZE signing_key message context randomness
  else
    if Libcrux_platform.Platform.simd128_support ()
    then
      Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.sign_pre_hashed_shake128 v_ROWS_IN_A
        v_COLUMNS_IN_A v_ROWS_X_COLUMNS v_ETA v_ERROR_RING_ELEMENT_SIZE v_GAMMA1_EXPONENT v_GAMMA2
        v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE
        v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT v_GAMMA1_RING_ELEMENT_SIZE
        v_SIGNING_KEY_SIZE v_SIGNATURE_SIZE signing_key message context randomness
    else
      Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.sign_pre_hashed_shake128 v_ROWS_IN_A
        v_COLUMNS_IN_A v_ROWS_X_COLUMNS v_ETA v_ERROR_RING_ELEMENT_SIZE v_GAMMA1_EXPONENT v_GAMMA2
        v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE
        v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT v_GAMMA1_RING_ELEMENT_SIZE
        v_SIGNING_KEY_SIZE v_SIGNATURE_SIZE signing_key message context randomness

let verify
      (v_ROWS_IN_A v_COLUMNS_IN_A v_ROWS_X_COLUMNS v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT v_GAMMA1_RING_ELEMENT_SIZE:
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
      v_ROWS_X_COLUMNS v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT
      v_GAMMA1_RING_ELEMENT_SIZE v_GAMMA2 v_BETA v_COMMITMENT_RING_ELEMENT_SIZE
      v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE
      v_MAX_ONES_IN_HINT verification_key_serialized message context signature_serialized
  else
    if Libcrux_platform.Platform.simd128_support ()
    then
      Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.verify v_ROWS_IN_A v_COLUMNS_IN_A
        v_ROWS_X_COLUMNS v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT
        v_GAMMA1_RING_ELEMENT_SIZE v_GAMMA2 v_BETA v_COMMITMENT_RING_ELEMENT_SIZE
        v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE
        v_MAX_ONES_IN_HINT verification_key_serialized message context signature_serialized
    else
      Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.verify v_ROWS_IN_A v_COLUMNS_IN_A
        v_ROWS_X_COLUMNS v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT
        v_GAMMA1_RING_ELEMENT_SIZE v_GAMMA2 v_BETA v_COMMITMENT_RING_ELEMENT_SIZE
        v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE
        v_MAX_ONES_IN_HINT verification_key_serialized message context signature_serialized

let verify_pre_hashed_shake128
      (v_ROWS_IN_A v_COLUMNS_IN_A v_ROWS_X_COLUMNS v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT v_GAMMA1_RING_ELEMENT_SIZE:
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
      v_COLUMNS_IN_A v_ROWS_X_COLUMNS v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT
      v_GAMMA1_RING_ELEMENT_SIZE v_GAMMA2 v_BETA v_COMMITMENT_RING_ELEMENT_SIZE
      v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE
      v_MAX_ONES_IN_HINT verification_key_serialized message context signature_serialized
  else
    if Libcrux_platform.Platform.simd128_support ()
    then
      Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.verify_pre_hashed_shake128 v_ROWS_IN_A
        v_COLUMNS_IN_A v_ROWS_X_COLUMNS v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT
        v_GAMMA1_RING_ELEMENT_SIZE v_GAMMA2 v_BETA v_COMMITMENT_RING_ELEMENT_SIZE
        v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE
        v_MAX_ONES_IN_HINT verification_key_serialized message context signature_serialized
    else
      Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.verify_pre_hashed_shake128 v_ROWS_IN_A
        v_COLUMNS_IN_A v_ROWS_X_COLUMNS v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT
        v_GAMMA1_RING_ELEMENT_SIZE v_GAMMA2 v_BETA v_COMMITMENT_RING_ELEMENT_SIZE
        v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE
        v_MAX_ONES_IN_HINT verification_key_serialized message context signature_serialized
