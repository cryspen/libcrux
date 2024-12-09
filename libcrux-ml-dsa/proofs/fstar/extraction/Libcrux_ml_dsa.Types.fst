module Libcrux_ml_dsa.Types
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let impl__len (v_SIZE: usize) (_: Prims.unit) = v_SIZE

let impl_2__len (v_SIZE: usize) (_: Prims.unit) = v_SIZE

let impl_4__len (v_SIZE: usize) (_: Prims.unit) = v_SIZE

let impl_4__as_raw (v_SIZE: usize) (self: t_MLDSASignature v_SIZE) = self.f_value

let impl_4__new (v_SIZE: usize) (value: t_Array u8 v_SIZE) =
  { f_value = value } <: t_MLDSASignature v_SIZE

let impl__as_raw (v_SIZE: usize) (self: t_MLDSASigningKey v_SIZE) = self.f_value

let impl__new (v_SIZE: usize) (value: t_Array u8 v_SIZE) =
  { f_value = value } <: t_MLDSASigningKey v_SIZE

let impl_2__as_raw (v_SIZE: usize) (self: t_MLDSAVerificationKey v_SIZE) = self.f_value

let impl_2__new (v_SIZE: usize) (value: t_Array u8 v_SIZE) =
  { f_value = value } <: t_MLDSAVerificationKey v_SIZE

let t_SigningError_cast_to_repr (x: t_SigningError) =
  match x with
  | SigningError_RejectionSamplingError  -> isz 0
  | SigningError_ContextTooLongError  -> isz 1

let t_VerificationError_cast_to_repr (x: t_VerificationError) =
  match x with
  | VerificationError_MalformedHintError  -> isz 0
  | VerificationError_SignerResponseExceedsBoundError  -> isz 1
  | VerificationError_CommitmentHashesDontMatchError  -> isz 3
  | VerificationError_VerificationContextTooLongError  -> isz 6

let impl__as_slice (v_SIZE: usize) (self: t_MLDSASigningKey v_SIZE) = self.f_value <: t_Slice u8

let impl_2__as_slice (v_SIZE: usize) (self: t_MLDSAVerificationKey v_SIZE) =
  self.f_value <: t_Slice u8

let impl_4__as_slice (v_SIZE: usize) (self: t_MLDSASignature v_SIZE) = self.f_value <: t_Slice u8
