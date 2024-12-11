module Libcrux_ml_dsa.Types
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

/// The number of bytes
val impl__len: v_SIZE: usize -> Prims.unit -> Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// The number of bytes
val impl_2__len: v_SIZE: usize -> Prims.unit
  -> Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// The number of bytes
val impl_4__len: v_SIZE: usize -> Prims.unit
  -> Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

///An ML-DSA signature.
type t_MLDSASignature (v_SIZE: usize) = { f_value:t_Array u8 v_SIZE }

/// A reference to the raw byte array.
val impl_4__as_ref (v_SIZE: usize) (self: t_MLDSASignature v_SIZE)
    : Prims.Pure (t_Array u8 v_SIZE) Prims.l_True (fun _ -> Prims.l_True)

/// Build
val impl_4__new (v_SIZE: usize) (value: t_Array u8 v_SIZE)
    : Prims.Pure (t_MLDSASignature v_SIZE) Prims.l_True (fun _ -> Prims.l_True)

///An ML-DSA signature key.
type t_MLDSASigningKey (v_SIZE: usize) = { f_value:t_Array u8 v_SIZE }

/// A reference to the raw byte array.
val impl__as_ref (v_SIZE: usize) (self: t_MLDSASigningKey v_SIZE)
    : Prims.Pure (t_Array u8 v_SIZE) Prims.l_True (fun _ -> Prims.l_True)

/// Build
val impl__new (v_SIZE: usize) (value: t_Array u8 v_SIZE)
    : Prims.Pure (t_MLDSASigningKey v_SIZE) Prims.l_True (fun _ -> Prims.l_True)

///An ML-DSA verification key.
type t_MLDSAVerificationKey (v_SIZE: usize) = { f_value:t_Array u8 v_SIZE }

/// A reference to the raw byte array.
val impl_2__as_ref (v_SIZE: usize) (self: t_MLDSAVerificationKey v_SIZE)
    : Prims.Pure (t_Array u8 v_SIZE) Prims.l_True (fun _ -> Prims.l_True)

/// Build
val impl_2__new (v_SIZE: usize) (value: t_Array u8 v_SIZE)
    : Prims.Pure (t_MLDSAVerificationKey v_SIZE) Prims.l_True (fun _ -> Prims.l_True)

/// An ML-DSA key pair.
type t_MLDSAKeyPair (v_VERIFICATION_KEY_SIZE: usize) (v_SIGNING_KEY_SIZE: usize) = {
  f_signing_key:t_MLDSASigningKey v_SIGNING_KEY_SIZE;
  f_verification_key:t_MLDSAVerificationKey v_VERIFICATION_KEY_SIZE
}

type t_SigningError =
  | SigningError_RejectionSamplingError : t_SigningError
  | SigningError_ContextTooLongError : t_SigningError

val t_SigningError_cast_to_repr (x: t_SigningError)
    : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

type t_VerificationError =
  | VerificationError_MalformedHintError : t_VerificationError
  | VerificationError_SignerResponseExceedsBoundError : t_VerificationError
  | VerificationError_CommitmentHashesDontMatchError : t_VerificationError
  | VerificationError_VerificationContextTooLongError : t_VerificationError

val t_VerificationError_cast_to_repr (x: t_VerificationError)
    : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

/// A reference to the raw byte slice.
val impl__as_slice (v_SIZE: usize) (self: t_MLDSASigningKey v_SIZE)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

/// A reference to the raw byte slice.
val impl_2__as_slice (v_SIZE: usize) (self: t_MLDSAVerificationKey v_SIZE)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

/// A reference to the raw byte slice.
val impl_4__as_slice (v_SIZE: usize) (self: t_MLDSASignature v_SIZE)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)
