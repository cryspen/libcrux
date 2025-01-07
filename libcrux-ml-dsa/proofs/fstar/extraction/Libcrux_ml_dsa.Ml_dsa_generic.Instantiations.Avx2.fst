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
  let open Libcrux_ml_dsa.Samplex4 in
  let open Libcrux_ml_dsa.Samplex4.Avx2 in
  let open Libcrux_ml_dsa.Simd.Avx2 in
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

let generate_key_pair_v44___inner
      (randomness: t_Array u8 (sz 32))
      (signing_key verification_key: t_Slice u8)
     =
  let tmp0, tmp1:(t_Slice u8 & t_Slice u8) =
    Libcrux_ml_dsa.Ml_dsa_generic.generate_key_pair_v44 #Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit
      #Libcrux_ml_dsa.Samplex4.Avx2.t_AVX2Sampler
      #Libcrux_ml_dsa.Hash_functions.Simd256.t_Shake128x4
      #Libcrux_ml_dsa.Hash_functions.Simd256.t_Shake256
      #Libcrux_ml_dsa.Hash_functions.Portable.t_Shake256Xof
      #Libcrux_ml_dsa.Hash_functions.Simd256.t_Shake256x4
      randomness
      signing_key
      verification_key
  in
  let signing_key:t_Slice u8 = tmp0 in
  let verification_key:t_Slice u8 = tmp1 in
  let _:Prims.unit = () in
  signing_key, verification_key <: (t_Slice u8 & t_Slice u8)

let generate_key_pair_v44
      (randomness: t_Array u8 (sz 32))
      (signing_key verification_key: t_Slice u8)
     =
  let tmp0, tmp1:(t_Slice u8 & t_Slice u8) =
    generate_key_pair_v44___inner randomness signing_key verification_key
  in
  let signing_key:t_Slice u8 = tmp0 in
  let verification_key:t_Slice u8 = tmp1 in
  let _:Prims.unit = () in
  let hax_temp_output:Prims.unit = () in
  signing_key, verification_key <: (t_Slice u8 & t_Slice u8)

let generate_key_pair_v65___inner
      (randomness: t_Array u8 (sz 32))
      (signing_key verification_key: t_Slice u8)
     =
  let tmp0, tmp1:(t_Slice u8 & t_Slice u8) =
    Libcrux_ml_dsa.Ml_dsa_generic.generate_key_pair_v65 #Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit
      #Libcrux_ml_dsa.Samplex4.Avx2.t_AVX2Sampler
      #Libcrux_ml_dsa.Hash_functions.Simd256.t_Shake128x4
      #Libcrux_ml_dsa.Hash_functions.Simd256.t_Shake256
      #Libcrux_ml_dsa.Hash_functions.Portable.t_Shake256Xof
      #Libcrux_ml_dsa.Hash_functions.Simd256.t_Shake256x4
      randomness
      signing_key
      verification_key
  in
  let signing_key:t_Slice u8 = tmp0 in
  let verification_key:t_Slice u8 = tmp1 in
  let _:Prims.unit = () in
  signing_key, verification_key <: (t_Slice u8 & t_Slice u8)

let generate_key_pair_v65
      (randomness: t_Array u8 (sz 32))
      (signing_key verification_key: t_Slice u8)
     =
  let tmp0, tmp1:(t_Slice u8 & t_Slice u8) =
    generate_key_pair_v65___inner randomness signing_key verification_key
  in
  let signing_key:t_Slice u8 = tmp0 in
  let verification_key:t_Slice u8 = tmp1 in
  let _:Prims.unit = () in
  let hax_temp_output:Prims.unit = () in
  signing_key, verification_key <: (t_Slice u8 & t_Slice u8)

let generate_key_pair_v87___inner
      (randomness: t_Array u8 (sz 32))
      (signing_key verification_key: t_Slice u8)
     =
  let tmp0, tmp1:(t_Slice u8 & t_Slice u8) =
    Libcrux_ml_dsa.Ml_dsa_generic.generate_key_pair_v87 #Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit
      #Libcrux_ml_dsa.Samplex4.Avx2.t_AVX2Sampler
      #Libcrux_ml_dsa.Hash_functions.Simd256.t_Shake128x4
      #Libcrux_ml_dsa.Hash_functions.Simd256.t_Shake256
      #Libcrux_ml_dsa.Hash_functions.Portable.t_Shake256Xof
      #Libcrux_ml_dsa.Hash_functions.Simd256.t_Shake256x4
      randomness
      signing_key
      verification_key
  in
  let signing_key:t_Slice u8 = tmp0 in
  let verification_key:t_Slice u8 = tmp1 in
  let _:Prims.unit = () in
  signing_key, verification_key <: (t_Slice u8 & t_Slice u8)

let generate_key_pair_v87
      (randomness: t_Array u8 (sz 32))
      (signing_key verification_key: t_Slice u8)
     =
  let tmp0, tmp1:(t_Slice u8 & t_Slice u8) =
    generate_key_pair_v87___inner randomness signing_key verification_key
  in
  let signing_key:t_Slice u8 = tmp0 in
  let verification_key:t_Slice u8 = tmp1 in
  let _:Prims.unit = () in
  let hax_temp_output:Prims.unit = () in
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
  Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Avx2.Avx2_feature.sign v_ROWS_IN_A v_COLUMNS_IN_A
    v_ROWS_X_COLUMNS v_ETA v_ERROR_RING_ELEMENT_SIZE v_GAMMA1_EXPONENT v_GAMMA2
    v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE
    v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT v_GAMMA1_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE
    v_SIGNATURE_SIZE signing_key message context randomness

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
  Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Avx2.Avx2_feature.sign_pre_hashed_shake128 v_ROWS_IN_A
    v_COLUMNS_IN_A v_ROWS_X_COLUMNS v_ETA v_ERROR_RING_ELEMENT_SIZE v_GAMMA1_EXPONENT v_GAMMA2
    v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE
    v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT v_GAMMA1_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE
    v_SIGNATURE_SIZE signing_key message context randomness

let verify
      (v_ROWS_IN_A v_COLUMNS_IN_A v_ROWS_X_COLUMNS v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT v_GAMMA1_RING_ELEMENT_SIZE:
          usize)
      (v_GAMMA2 v_BETA: i32)
      (v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT:
          usize)
      (verification_key: t_Array u8 v_VERIFICATION_KEY_SIZE)
      (message context: t_Slice u8)
      (signature: t_Array u8 v_SIGNATURE_SIZE)
     =
  Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Avx2.Avx2_feature.verify v_ROWS_IN_A v_COLUMNS_IN_A
    v_ROWS_X_COLUMNS v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT
    v_GAMMA1_RING_ELEMENT_SIZE v_GAMMA2 v_BETA v_COMMITMENT_RING_ELEMENT_SIZE
    v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT
    verification_key message context signature

let verify_pre_hashed_shake128
      (v_ROWS_IN_A v_COLUMNS_IN_A v_ROWS_X_COLUMNS v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT v_GAMMA1_RING_ELEMENT_SIZE:
          usize)
      (v_GAMMA2 v_BETA: i32)
      (v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT:
          usize)
      (verification_key: t_Array u8 v_VERIFICATION_KEY_SIZE)
      (message context: t_Slice u8)
      (signature: t_Array u8 v_SIGNATURE_SIZE)
     =
  Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Avx2.Avx2_feature.verify_pre_hashed_shake128 v_ROWS_IN_A
    v_COLUMNS_IN_A v_ROWS_X_COLUMNS v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT
    v_GAMMA1_RING_ELEMENT_SIZE v_GAMMA2 v_BETA v_COMMITMENT_RING_ELEMENT_SIZE
    v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT
    verification_key message context signature
