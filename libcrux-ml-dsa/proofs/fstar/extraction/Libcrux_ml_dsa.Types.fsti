module Libcrux_ml_dsa.Types
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

/// The number of bytes
val impl__len: v_SIZE: usize -> Prims.unit -> Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// The number of bytes
val impl_2__len: v_SIZE: usize -> Prims.unit
  -> Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// The number of bytes
val impl_4__len: v_SIZE: usize -> Prims.unit
  -> Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

type t_SigningError =
  | SigningError_RejectionSamplingError : t_SigningError
  | SigningError_ContextTooLongError : t_SigningError

val t_SigningError_cast_to_repr (x: t_SigningError)
    : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

type t_VerificationError =
  | VerificationError_MalformedHintError : t_VerificationError
  | VerificationError_SignerResponseExceedsBoundError : t_VerificationError
  | VerificationError_CommitmentHashesDontMatchError : t_VerificationError
  | VerificationError_ContextTooLongError : t_VerificationError

val t_VerificationError_cast_to_repr (x: t_VerificationError)
    : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

///An ML-DSA signature.
type t_MLDSASignature (v_SIZE: usize) =
  | MLDSASignature : t_Array u8 v_SIZE -> t_MLDSASignature v_SIZE

/// A reference to the raw byte slice.
val impl_4__as_slice (v_SIZE: usize) (self: t_MLDSASignature v_SIZE)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

///An ML-DSA signature key.
type t_MLDSASigningKey (v_SIZE: usize) =
  | MLDSASigningKey : t_Array u8 v_SIZE -> t_MLDSASigningKey v_SIZE

/// A reference to the raw byte slice.
val impl__as_slice (v_SIZE: usize) (self: t_MLDSASigningKey v_SIZE)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

///An ML-DSA verification key.
type t_MLDSAVerificationKey (v_SIZE: usize) =
  | MLDSAVerificationKey : t_Array u8 v_SIZE -> t_MLDSAVerificationKey v_SIZE

/// A reference to the raw byte slice.
val impl_2__as_slice (v_SIZE: usize) (self: t_MLDSAVerificationKey v_SIZE)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

/// An ML-DSA key pair.
type t_MLDSAKeyPair (v_VERIFICATION_KEY_SIZE: usize) (v_SIGNING_KEY_SIZE: usize) = {
  f_signing_key:t_MLDSASigningKey v_SIGNING_KEY_SIZE;
  f_verification_key:t_MLDSAVerificationKey v_VERIFICATION_KEY_SIZE
}

type t_Signature
  (v_SIMDUnit: Type0) (v_COMMITMENT_HASH_SIZE: usize) (v_COLUMNS_IN_A: usize) (v_ROWS_IN_A: usize)
  {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
  = {
  f_commitment_hash:t_Array u8 v_COMMITMENT_HASH_SIZE;
  f_signer_response:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    v_COLUMNS_IN_A;
  f_hint:t_Array (t_Array i32 (Rust_primitives.mk_usize 256)) v_ROWS_IN_A
}
