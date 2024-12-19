module Libcrux_ml_dsa.Ml_dsa_generic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Hash_functions.Shake128 in
  let open Libcrux_ml_dsa.Hash_functions.Shake256 in
  let open Libcrux_ml_dsa.Pre_hash in
  let open Libcrux_ml_dsa.Samplex4 in
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

/// This corresponds to line 6 in algorithm 7 in FIPS 204 (line 7 in algorithm
/// 8, resp.).
/// If `domain_separation_context` is supplied, applies domain
/// separation and length encoding to the context string,
/// before appending the message (in the regular variant) or the
/// pre-hash OID as well as the pre-hashed message digest. Otherwise,
/// it is assumed that `message` already contains domain separation
/// information.
/// In FIPS 204 M' is the concatenation of the domain separated context, any
/// potential pre-hash OID and the message (or the message pre-hash). We do not
/// explicitely construct the concatenation in memory since it is of statically unknown
/// length, but feed its components directly into the incremental XOF.
/// Refer to line 10 of Algorithm 2 (and line 5 of Algorithm 3, resp.) in [FIPS
/// 204](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.204.pdf#section.5)
/// for details on the domain separation for regular ML-DSA. Line
/// 23 of Algorithm 4 (and line 18 of Algorithm 5,resp.) describe domain separation for the HashMl-DSA
/// variant.
val derive_message_representative
      (#v_Shake256Xof: Type0)
      {| i1: Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256Xof |}
      (verification_key_hash: t_Array u8 (sz 64))
      (domain_separation_context:
          Core.Option.t_Option Libcrux_ml_dsa.Pre_hash.t_DomainSeparationContext)
      (message: t_Slice u8)
      (message_representative: t_Array u8 (sz 64))
    : Prims.Pure (t_Array u8 (sz 64)) Prims.l_True (fun _ -> Prims.l_True)

/// The internal verification API.
/// If no `domain_separation_context` is supplied, it is assumed that
/// `message` already contains the domain separation.
val verify_internal
      (#v_SIMDUnit #v_Sampler #v_Shake128X4 #v_Shake256 #v_Shake256Xof: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT v_GAMMA1_RING_ELEMENT_SIZE:
          usize)
      (v_GAMMA2 v_BETA: i32)
      (v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT:
          usize)
      {| i5: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i6: Libcrux_ml_dsa.Samplex4.t_X4Sampler v_Sampler |}
      {| i7: Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4 |}
      {| i8: Libcrux_ml_dsa.Hash_functions.Shake256.t_DsaXof v_Shake256 |}
      {| i9: Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256Xof |}
      (verification_key_serialized: t_Array u8 v_VERIFICATION_KEY_SIZE)
      (message: t_Slice u8)
      (domain_separation_context:
          Core.Option.t_Option Libcrux_ml_dsa.Pre_hash.t_DomainSeparationContext)
      (signature_serialized: t_Array u8 v_SIGNATURE_SIZE)
    : Prims.Pure (Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError)
      Prims.l_True
      (fun _ -> Prims.l_True)

val verify
      (#v_SIMDUnit #v_Sampler #v_Shake128X4 #v_Shake256 #v_Shake256Xof: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT v_GAMMA1_RING_ELEMENT_SIZE:
          usize)
      (v_GAMMA2 v_BETA: i32)
      (v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT:
          usize)
      {| i5: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i6: Libcrux_ml_dsa.Samplex4.t_X4Sampler v_Sampler |}
      {| i7: Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4 |}
      {| i8: Libcrux_ml_dsa.Hash_functions.Shake256.t_DsaXof v_Shake256 |}
      {| i9: Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256Xof |}
      (verification_key_serialized: t_Array u8 v_VERIFICATION_KEY_SIZE)
      (message context: t_Slice u8)
      (signature_serialized: t_Array u8 v_SIGNATURE_SIZE)
    : Prims.Pure (Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError)
      Prims.l_True
      (fun _ -> Prims.l_True)

val verify_pre_hashed
      (#v_SIMDUnit #v_Sampler #v_Shake128 #v_Shake128X4 #v_Shake256 #v_Shake256Xof #v_PH: Type0)
      (v_PH_DIGEST_LEN v_ROWS_IN_A v_COLUMNS_IN_A v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT v_GAMMA1_RING_ELEMENT_SIZE:
          usize)
      (v_GAMMA2 v_BETA: i32)
      (v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT:
          usize)
      {| i7: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i8: Libcrux_ml_dsa.Samplex4.t_X4Sampler v_Sampler |}
      {| i9: Libcrux_ml_dsa.Hash_functions.Shake128.t_Xof v_Shake128 |}
      {| i10: Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4 |}
      {| i11: Libcrux_ml_dsa.Hash_functions.Shake256.t_DsaXof v_Shake256 |}
      {| i12: Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256Xof |}
      {| i13: Libcrux_ml_dsa.Pre_hash.t_PreHash v_PH v_PH_DIGEST_LEN |}
      (verification_key_serialized: t_Array u8 v_VERIFICATION_KEY_SIZE)
      (message context: t_Slice u8)
      (signature_serialized: t_Array u8 v_SIGNATURE_SIZE)
    : Prims.Pure (Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// The internal signing API.
/// If no `domain_separation_context` is supplied, it is assumed that
/// `message` already contains the domain separation.
val sign_internal
      (#v_SIMDUnit #v_Sampler #v_Shake128X4 #v_Shake256 #v_Shake256Xof #v_Shake256X4: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A v_ETA v_ERROR_RING_ELEMENT_SIZE v_GAMMA1_EXPONENT: usize)
      (v_GAMMA2: i32)
      (v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT v_GAMMA1_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE v_SIGNATURE_SIZE:
          usize)
      {| i6: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i7: Libcrux_ml_dsa.Samplex4.t_X4Sampler v_Sampler |}
      {| i8: Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4 |}
      {| i9: Libcrux_ml_dsa.Hash_functions.Shake256.t_DsaXof v_Shake256 |}
      {| i10: Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256Xof |}
      {| i11: Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4 |}
      (signing_key: t_Array u8 v_SIGNING_KEY_SIZE)
      (message: t_Slice u8)
      (domain_separation_context:
          Core.Option.t_Option Libcrux_ml_dsa.Pre_hash.t_DomainSeparationContext)
      (randomness: t_Array u8 (sz 32))
    : Prims.Pure
      (Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature v_SIGNATURE_SIZE)
          Libcrux_ml_dsa.Types.t_SigningError) Prims.l_True (fun _ -> Prims.l_True)

val sign
      (#v_SIMDUnit #v_Sampler #v_Shake128X4 #v_Shake256 #v_Shake256Xof #v_Shake256X4: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A v_ETA v_ERROR_RING_ELEMENT_SIZE v_GAMMA1_EXPONENT: usize)
      (v_GAMMA2: i32)
      (v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT v_GAMMA1_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE v_SIGNATURE_SIZE:
          usize)
      {| i6: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i7: Libcrux_ml_dsa.Samplex4.t_X4Sampler v_Sampler |}
      {| i8: Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4 |}
      {| i9: Libcrux_ml_dsa.Hash_functions.Shake256.t_DsaXof v_Shake256 |}
      {| i10: Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256Xof |}
      {| i11: Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4 |}
      (signing_key: t_Array u8 v_SIGNING_KEY_SIZE)
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
    : Prims.Pure
      (Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature v_SIGNATURE_SIZE)
          Libcrux_ml_dsa.Types.t_SigningError) Prims.l_True (fun _ -> Prims.l_True)

val sign_pre_hashed
      (#v_SIMDUnit #v_Sampler #v_Shake128 #v_Shake128X4 #v_Shake256 #v_Shake256Xof #v_Shake256X4 #v_PH:
          Type0)
      (v_PH_DIGEST_LEN v_ROWS_IN_A v_COLUMNS_IN_A v_ETA v_ERROR_RING_ELEMENT_SIZE v_GAMMA1_EXPONENT:
          usize)
      (v_GAMMA2: i32)
      (v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT v_GAMMA1_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE v_SIGNATURE_SIZE:
          usize)
      {| i8: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i9: Libcrux_ml_dsa.Samplex4.t_X4Sampler v_Sampler |}
      {| i10: Libcrux_ml_dsa.Hash_functions.Shake128.t_Xof v_Shake128 |}
      {| i11: Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4 |}
      {| i12: Libcrux_ml_dsa.Hash_functions.Shake256.t_DsaXof v_Shake256 |}
      {| i13: Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256Xof |}
      {| i14: Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4 |}
      {| i15: Libcrux_ml_dsa.Pre_hash.t_PreHash v_PH v_PH_DIGEST_LEN |}
      (signing_key: t_Array u8 v_SIGNING_KEY_SIZE)
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
    : Prims.Pure
      (Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature v_SIGNATURE_SIZE)
          Libcrux_ml_dsa.Types.t_SigningError) Prims.l_True (fun _ -> Prims.l_True)

/// Generate a key pair.
val generate_key_pair
      (#v_SIMDUnit #v_Sampler #v_Shake128X4 #v_Shake256 #v_Shake256Xof #v_Shake256X4: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A v_ETA v_ERROR_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE v_VERIFICATION_KEY_SIZE:
          usize)
      {| i6: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i7: Libcrux_ml_dsa.Samplex4.t_X4Sampler v_Sampler |}
      {| i8: Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4 |}
      {| i9: Libcrux_ml_dsa.Hash_functions.Shake256.t_DsaXof v_Shake256 |}
      {| i10: Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256Xof |}
      {| i11: Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4 |}
      (randomness: t_Array u8 (sz 32))
    : Prims.Pure (t_Array u8 v_SIGNING_KEY_SIZE & t_Array u8 v_VERIFICATION_KEY_SIZE)
      Prims.l_True
      (fun _ -> Prims.l_True)
