module Libcrux_ml_dsa.Types
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

///An ML-DSA signature key.
type t_MLDSASigningKey (v_SIZE: usize) = { f_value:t_Array u8 v_SIZE }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': v_SIZE: usize -> Core.Clone.t_Clone (t_MLDSASigningKey v_SIZE)

let impl_1 (v_SIZE: usize) = impl_1' v_SIZE

/// Init with zero
let impl__zero (v_SIZE: usize) (_: Prims.unit) : t_MLDSASigningKey v_SIZE =
  { f_value = Rust_primitives.Hax.repeat (mk_u8 0) v_SIZE } <: t_MLDSASigningKey v_SIZE

/// Build
let impl__new (v_SIZE: usize) (value: t_Array u8 v_SIZE) : t_MLDSASigningKey v_SIZE =
  { f_value = value } <: t_MLDSASigningKey v_SIZE

/// A reference to the raw byte slice.
let impl__as_slice (v_SIZE: usize) (self: t_MLDSASigningKey v_SIZE) : t_Slice u8 =
  self.f_value <: t_Slice u8

/// A reference to the raw byte array.
let impl__as_ref (v_SIZE: usize) (self: t_MLDSASigningKey v_SIZE) : t_Array u8 v_SIZE = self.f_value

/// The number of bytes
let impl__len (v_SIZE: usize) (_: Prims.unit) : usize = v_SIZE

///An ML-DSA verification key.
type t_MLDSAVerificationKey (v_SIZE: usize) = { f_value:t_Array u8 v_SIZE }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': v_SIZE: usize -> Core.Clone.t_Clone (t_MLDSAVerificationKey v_SIZE)

let impl_3 (v_SIZE: usize) = impl_3' v_SIZE

/// Init with zero
let impl_2__zero (v_SIZE: usize) (_: Prims.unit) : t_MLDSAVerificationKey v_SIZE =
  { f_value = Rust_primitives.Hax.repeat (mk_u8 0) v_SIZE } <: t_MLDSAVerificationKey v_SIZE

/// Build
let impl_2__new (v_SIZE: usize) (value: t_Array u8 v_SIZE) : t_MLDSAVerificationKey v_SIZE =
  { f_value = value } <: t_MLDSAVerificationKey v_SIZE

/// A reference to the raw byte slice.
let impl_2__as_slice (v_SIZE: usize) (self: t_MLDSAVerificationKey v_SIZE) : t_Slice u8 =
  self.f_value <: t_Slice u8

/// A reference to the raw byte array.
let impl_2__as_ref (v_SIZE: usize) (self: t_MLDSAVerificationKey v_SIZE) : t_Array u8 v_SIZE =
  self.f_value

/// The number of bytes
let impl_2__len (v_SIZE: usize) (_: Prims.unit) : usize = v_SIZE

///An ML-DSA signature.
type t_MLDSASignature (v_SIZE: usize) = { f_value:t_Array u8 v_SIZE }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_5': v_SIZE: usize -> Core.Clone.t_Clone (t_MLDSASignature v_SIZE)

let impl_5 (v_SIZE: usize) = impl_5' v_SIZE

/// Init with zero
let impl_4__zero (v_SIZE: usize) (_: Prims.unit) : t_MLDSASignature v_SIZE =
  { f_value = Rust_primitives.Hax.repeat (mk_u8 0) v_SIZE } <: t_MLDSASignature v_SIZE

/// Build
let impl_4__new (v_SIZE: usize) (value: t_Array u8 v_SIZE) : t_MLDSASignature v_SIZE =
  { f_value = value } <: t_MLDSASignature v_SIZE

/// A reference to the raw byte slice.
let impl_4__as_slice (v_SIZE: usize) (self: t_MLDSASignature v_SIZE) : t_Slice u8 =
  self.f_value <: t_Slice u8

/// A reference to the raw byte array.
let impl_4__as_ref (v_SIZE: usize) (self: t_MLDSASignature v_SIZE) : t_Array u8 v_SIZE =
  self.f_value

/// The number of bytes
let impl_4__len (v_SIZE: usize) (_: Prims.unit) : usize = v_SIZE

/// An ML-DSA key pair.
type t_MLDSAKeyPair (v_VERIFICATION_KEY_SIZE: usize) (v_SIGNING_KEY_SIZE: usize) = {
  f_signing_key:t_MLDSASigningKey v_SIGNING_KEY_SIZE;
  f_verification_key:t_MLDSAVerificationKey v_VERIFICATION_KEY_SIZE
}

type t_VerificationError =
  | VerificationError_MalformedHintError : t_VerificationError
  | VerificationError_SignerResponseExceedsBoundError : t_VerificationError
  | VerificationError_CommitmentHashesDontMatchError : t_VerificationError
  | VerificationError_VerificationContextTooLongError : t_VerificationError

let t_VerificationError_cast_to_repr (x: t_VerificationError) : isize =
  match x <: t_VerificationError with
  | VerificationError_MalformedHintError  -> mk_isize 0
  | VerificationError_SignerResponseExceedsBoundError  -> mk_isize 1
  | VerificationError_CommitmentHashesDontMatchError  -> mk_isize 2
  | VerificationError_VerificationContextTooLongError  -> mk_isize 3

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_6': Core.Fmt.t_Debug t_VerificationError

let impl_6 = impl_6'

type t_SigningError =
  | SigningError_RejectionSamplingError : t_SigningError
  | SigningError_ContextTooLongError : t_SigningError

let t_SigningError_cast_to_repr (x: t_SigningError) : isize =
  match x <: t_SigningError with
  | SigningError_RejectionSamplingError  -> mk_isize 0
  | SigningError_ContextTooLongError  -> mk_isize 1

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_7': Core.Fmt.t_Debug t_SigningError

let impl_7 = impl_7'
