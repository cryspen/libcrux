module Libcrux_ml_dsa.Ml_dsa_generic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Hash_functions.Shake128 in
  let open Libcrux_ml_dsa.Hash_functions.Shake256 in
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

type t_SigningError = | SigningError_RejectionSamplingError : t_SigningError

val t_SigningError_cast_to_repr (x: t_SigningError)
    : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

type t_VerificationError =
  | VerificationError_MalformedHintError : t_VerificationError
  | VerificationError_SignerResponseExceedsBoundError : t_VerificationError
  | VerificationError_CommitmentHashesDontMatchError : t_VerificationError

val t_VerificationError_cast_to_repr (x: t_VerificationError)
    : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

val sign:
    #v_SIMDUnit: Type0 ->
    #v_Shake128X4: Type0 ->
    #v_Shake256: Type0 ->
    #v_Shake256X4: Type0 ->
    v_ROWS_IN_A: usize ->
    v_COLUMNS_IN_A: usize ->
    v_ETA: usize ->
    v_ERROR_RING_ELEMENT_SIZE: usize ->
    v_GAMMA1_EXPONENT: usize ->
    v_GAMMA2: i32 ->
    v_COMMITMENT_RING_ELEMENT_SIZE: usize ->
    v_COMMITMENT_VECTOR_SIZE: usize ->
    v_COMMITMENT_HASH_SIZE: usize ->
    v_ONES_IN_VERIFIER_CHALLENGE: usize ->
    v_MAX_ONES_IN_HINT: usize ->
    v_GAMMA1_RING_ELEMENT_SIZE: usize ->
    v_SIGNING_KEY_SIZE: usize ->
    v_SIGNATURE_SIZE: usize ->
    {| i4: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |} ->
    {| i5: Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4 |} ->
    {| i6: Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256 |} ->
    {| i7: Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4 |} ->
    Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val verify:
    #v_SIMDUnit: Type0 ->
    #v_Shake128X4: Type0 ->
    #v_Shake256: Type0 ->
    v_ROWS_IN_A: usize ->
    v_COLUMNS_IN_A: usize ->
    v_SIGNATURE_SIZE: usize ->
    v_VERIFICATION_KEY_SIZE: usize ->
    v_GAMMA1_EXPONENT: usize ->
    v_GAMMA1_RING_ELEMENT_SIZE: usize ->
    v_GAMMA2: i32 ->
    v_BETA: i32 ->
    v_COMMITMENT_RING_ELEMENT_SIZE: usize ->
    v_COMMITMENT_VECTOR_SIZE: usize ->
    v_COMMITMENT_HASH_SIZE: usize ->
    v_ONES_IN_VERIFIER_CHALLENGE: usize ->
    v_MAX_ONES_IN_HINT: usize ->
    {| i3: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |} ->
    {| i4: Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4 |} ->
    {| i5: Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256 |} ->
    Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

/// Generate a key pair.
val generate_key_pair
      (#v_SIMDUnit #v_Shake128X4 #v_Shake256 #v_Shake256X4: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A v_ETA v_ERROR_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE v_VERIFICATION_KEY_SIZE:
          usize)
      {| i4: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i5: Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4 |}
      {| i6: Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256 |}
      {| i7: Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4 |}
      (randomness: t_Array u8 (Rust_primitives.mk_usize 32))
    : Prims.Pure (t_Array u8 v_SIGNING_KEY_SIZE & t_Array u8 v_VERIFICATION_KEY_SIZE)
      Prims.l_True
      (fun _ -> Prims.l_True)

type t_Signature
  (v_SIMDUnit: Type0) (v_COMMITMENT_HASH_SIZE: usize) (v_COLUMNS_IN_A: usize) (v_ROWS_IN_A: usize)
  {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
  = {
  f_commitment_hash:t_Array u8 v_COMMITMENT_HASH_SIZE;
  f_signer_response:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    v_COLUMNS_IN_A;
  f_hint:t_Array (t_Array i32 (Rust_primitives.mk_usize 256)) v_ROWS_IN_A
}
