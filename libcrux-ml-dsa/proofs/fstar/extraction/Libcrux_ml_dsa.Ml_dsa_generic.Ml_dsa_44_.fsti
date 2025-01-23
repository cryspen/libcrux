module Libcrux_ml_dsa.Ml_dsa_generic.Ml_dsa_44_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Hash_functions.Shake128 in
  let open Libcrux_ml_dsa.Hash_functions.Shake256 in
  let open Libcrux_ml_dsa.Polynomial in
  let open Libcrux_ml_dsa.Pre_hash in
  let open Libcrux_ml_dsa.Samplex4 in
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

let v_BETA: i32 =
  Libcrux_ml_dsa.Constants.beta Libcrux_ml_dsa.Constants.Ml_dsa_44_.v_ONES_IN_VERIFIER_CHALLENGE
    Libcrux_ml_dsa.Constants.Ml_dsa_44_.v_ETA

let v_COMMITMENT_RING_ELEMENT_SIZE: usize =
  Libcrux_ml_dsa.Constants.commitment_ring_element_size Libcrux_ml_dsa.Constants.Ml_dsa_44_.v_BITS_PER_COMMITMENT_COEFFICIENT

let v_COMMITMENT_VECTOR_SIZE: usize =
  Libcrux_ml_dsa.Constants.commitment_vector_size Libcrux_ml_dsa.Constants.Ml_dsa_44_.v_BITS_PER_COMMITMENT_COEFFICIENT
    Libcrux_ml_dsa.Constants.Ml_dsa_44_.v_ROWS_IN_A

let v_ERROR_RING_ELEMENT_SIZE: usize =
  Libcrux_ml_dsa.Constants.error_ring_element_size Libcrux_ml_dsa.Constants.Ml_dsa_44_.v_BITS_PER_ERROR_COEFFICIENT

let v_GAMMA1_RING_ELEMENT_SIZE: usize =
  Libcrux_ml_dsa.Constants.gamma1_ring_element_size Libcrux_ml_dsa.Constants.Ml_dsa_44_.v_BITS_PER_GAMMA1_COEFFICIENT

let v_ROW_COLUMN: usize =
  Libcrux_ml_dsa.Constants.Ml_dsa_44_.v_ROWS_IN_A +!
  Libcrux_ml_dsa.Constants.Ml_dsa_44_.v_COLUMNS_IN_A

let v_ROW_X_COLUMN: usize =
  Libcrux_ml_dsa.Constants.Ml_dsa_44_.v_ROWS_IN_A *!
  Libcrux_ml_dsa.Constants.Ml_dsa_44_.v_COLUMNS_IN_A

let v_SIGNATURE_SIZE: usize =
  Libcrux_ml_dsa.Constants.signature_size Libcrux_ml_dsa.Constants.Ml_dsa_44_.v_ROWS_IN_A
    Libcrux_ml_dsa.Constants.Ml_dsa_44_.v_COLUMNS_IN_A
    Libcrux_ml_dsa.Constants.Ml_dsa_44_.v_MAX_ONES_IN_HINT
    Libcrux_ml_dsa.Constants.Ml_dsa_44_.v_COMMITMENT_HASH_SIZE
    Libcrux_ml_dsa.Constants.Ml_dsa_44_.v_BITS_PER_GAMMA1_COEFFICIENT

let v_SIGNING_KEY_SIZE: usize =
  Libcrux_ml_dsa.Constants.signing_key_size Libcrux_ml_dsa.Constants.Ml_dsa_44_.v_ROWS_IN_A
    Libcrux_ml_dsa.Constants.Ml_dsa_44_.v_COLUMNS_IN_A
    v_ERROR_RING_ELEMENT_SIZE

let v_VERIFICATION_KEY_SIZE: usize =
  Libcrux_ml_dsa.Constants.verification_key_size Libcrux_ml_dsa.Constants.Ml_dsa_44_.v_ROWS_IN_A

/// The internal verification API.
/// If no `domain_separation_context` is supplied, it is assumed that
/// `message` already contains the domain separation.
val verify_internal
      (#v_SIMDUnit #v_Sampler #v_Shake128X4 #v_Shake256 #v_Shake256Xof: Type0)
      {| i5: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i6: Libcrux_ml_dsa.Samplex4.t_X4Sampler v_Sampler |}
      {| i7: Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4 |}
      {| i8: Libcrux_ml_dsa.Hash_functions.Shake256.t_DsaXof v_Shake256 |}
      {| i9: Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256Xof |}
      (verification_key: t_Array u8 (mk_usize 1312))
      (message: t_Slice u8)
      (domain_separation_context:
          Core.Option.t_Option Libcrux_ml_dsa.Pre_hash.t_DomainSeparationContext)
      (signature_serialized: t_Array u8 (mk_usize 2420))
    : Prims.Pure (Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError)
      Prims.l_True
      (fun _ -> Prims.l_True)

val verify
      (#v_SIMDUnit #v_Sampler #v_Shake128X4 #v_Shake256 #v_Shake256Xof: Type0)
      {| i5: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i6: Libcrux_ml_dsa.Samplex4.t_X4Sampler v_Sampler |}
      {| i7: Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4 |}
      {| i8: Libcrux_ml_dsa.Hash_functions.Shake256.t_DsaXof v_Shake256 |}
      {| i9: Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256Xof |}
      (verification_key_serialized: t_Array u8 (mk_usize 1312))
      (message context: t_Slice u8)
      (signature_serialized: t_Array u8 (mk_usize 2420))
    : Prims.Pure (Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError)
      Prims.l_True
      (fun _ -> Prims.l_True)

val verify_pre_hashed
      (#v_SIMDUnit #v_Sampler #v_Shake128 #v_Shake128X4 #v_Shake256 #v_Shake256Xof #v_PH: Type0)
      {| i7: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i8: Libcrux_ml_dsa.Samplex4.t_X4Sampler v_Sampler |}
      {| i9: Libcrux_ml_dsa.Hash_functions.Shake128.t_Xof v_Shake128 |}
      {| i10: Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4 |}
      {| i11: Libcrux_ml_dsa.Hash_functions.Shake256.t_DsaXof v_Shake256 |}
      {| i12: Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256Xof |}
      {| i13: Libcrux_ml_dsa.Pre_hash.t_PreHash v_PH |}
      (verification_key_serialized: t_Array u8 (mk_usize 1312))
      (message context pre_hash_buffer: t_Slice u8)
      (signature_serialized: t_Array u8 (mk_usize 2420))
    : Prims.Pure
      (t_Slice u8 & Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError)
      Prims.l_True
      (fun _ -> Prims.l_True)

val sign_internal
      (#v_SIMDUnit #v_Sampler #v_Shake128X4 #v_Shake256 #v_Shake256Xof #v_Shake256X4: Type0)
      {| i6: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i7: Libcrux_ml_dsa.Samplex4.t_X4Sampler v_Sampler |}
      {| i8: Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4 |}
      {| i9: Libcrux_ml_dsa.Hash_functions.Shake256.t_DsaXof v_Shake256 |}
      {| i10: Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256Xof |}
      {| i11: Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4 |}
      (signing_key message: t_Slice u8)
      (domain_separation_context:
          Core.Option.t_Option Libcrux_ml_dsa.Pre_hash.t_DomainSeparationContext)
      (randomness: t_Array u8 (mk_usize 32))
      (signature: t_Array u8 (mk_usize 2420))
    : Prims.Pure
      (t_Array u8 (mk_usize 2420) &
        Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_SigningError)
      Prims.l_True
      (fun _ -> Prims.l_True)

val sign_mut
      (#v_SIMDUnit #v_Sampler #v_Shake128X4 #v_Shake256 #v_Shake256Xof #v_Shake256X4: Type0)
      {| i6: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i7: Libcrux_ml_dsa.Samplex4.t_X4Sampler v_Sampler |}
      {| i8: Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4 |}
      {| i9: Libcrux_ml_dsa.Hash_functions.Shake256.t_DsaXof v_Shake256 |}
      {| i10: Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256Xof |}
      {| i11: Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4 |}
      (signing_key message context: t_Slice u8)
      (randomness: t_Array u8 (mk_usize 32))
      (signature: t_Array u8 (mk_usize 2420))
    : Prims.Pure
      (t_Array u8 (mk_usize 2420) &
        Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_SigningError)
      Prims.l_True
      (fun _ -> Prims.l_True)

val sign
      (#v_SIMDUnit #v_Sampler #v_Shake128X4 #v_Shake256 #v_Shake256Xof #v_Shake256X4: Type0)
      {| i6: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i7: Libcrux_ml_dsa.Samplex4.t_X4Sampler v_Sampler |}
      {| i8: Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4 |}
      {| i9: Libcrux_ml_dsa.Hash_functions.Shake256.t_DsaXof v_Shake256 |}
      {| i10: Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256Xof |}
      {| i11: Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4 |}
      (signing_key message context: t_Slice u8)
      (randomness: t_Array u8 (mk_usize 32))
    : Prims.Pure
      (Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (mk_usize 2420))
          Libcrux_ml_dsa.Types.t_SigningError) Prims.l_True (fun _ -> Prims.l_True)

val sign_pre_hashed_mut
      (#v_SIMDUnit #v_Sampler #v_Shake128 #v_Shake128X4 #v_Shake256 #v_Shake256Xof #v_Shake256X4 #v_PH:
          Type0)
      {| i8: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i9: Libcrux_ml_dsa.Samplex4.t_X4Sampler v_Sampler |}
      {| i10: Libcrux_ml_dsa.Hash_functions.Shake128.t_Xof v_Shake128 |}
      {| i11: Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4 |}
      {| i12: Libcrux_ml_dsa.Hash_functions.Shake256.t_DsaXof v_Shake256 |}
      {| i13: Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256Xof |}
      {| i14: Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4 |}
      {| i15: Libcrux_ml_dsa.Pre_hash.t_PreHash v_PH |}
      (signing_key message context pre_hash_buffer: t_Slice u8)
      (randomness: t_Array u8 (mk_usize 32))
      (signature: t_Array u8 (mk_usize 2420))
    : Prims.Pure
      (t_Slice u8 & t_Array u8 (mk_usize 2420) &
        Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_SigningError)
      Prims.l_True
      (fun _ -> Prims.l_True)

val sign_pre_hashed
      (#v_SIMDUnit #v_Sampler #v_Shake128 #v_Shake128X4 #v_Shake256 #v_Shake256Xof #v_Shake256X4 #v_PH:
          Type0)
      {| i8: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i9: Libcrux_ml_dsa.Samplex4.t_X4Sampler v_Sampler |}
      {| i10: Libcrux_ml_dsa.Hash_functions.Shake128.t_Xof v_Shake128 |}
      {| i11: Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4 |}
      {| i12: Libcrux_ml_dsa.Hash_functions.Shake256.t_DsaXof v_Shake256 |}
      {| i13: Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256Xof |}
      {| i14: Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4 |}
      {| i15: Libcrux_ml_dsa.Pre_hash.t_PreHash v_PH |}
      (signing_key message context pre_hash_buffer: t_Slice u8)
      (randomness: t_Array u8 (mk_usize 32))
    : Prims.Pure
      (t_Slice u8 &
        Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (mk_usize 2420))
          Libcrux_ml_dsa.Types.t_SigningError) Prims.l_True (fun _ -> Prims.l_True)

val generate_key_pair
      (#v_SIMDUnit #v_Sampler #v_Shake128X4 #v_Shake256 #v_Shake256Xof #v_Shake256X4: Type0)
      {| i6: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i7: Libcrux_ml_dsa.Samplex4.t_X4Sampler v_Sampler |}
      {| i8: Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4 |}
      {| i9: Libcrux_ml_dsa.Hash_functions.Shake256.t_DsaXof v_Shake256 |}
      {| i10: Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256Xof |}
      {| i11: Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4 |}
      (randomness: t_Array u8 (mk_usize 32))
      (signing_key verification_key: t_Slice u8)
    : Prims.Pure (t_Slice u8 & t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)
