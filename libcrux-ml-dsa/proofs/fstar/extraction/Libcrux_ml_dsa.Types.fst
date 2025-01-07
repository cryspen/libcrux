module Libcrux_ml_dsa.Types
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let impl__len (v_SIZE: usize) (_: Prims.unit) = v_SIZE

let impl_2__len (v_SIZE: usize) (_: Prims.unit) = v_SIZE

let impl_4__len (v_SIZE: usize) (_: Prims.unit) = v_SIZE

let impl_4__as_ref (v_SIZE: usize) (self: t_MLDSASignature v_SIZE) = self.f_value

let impl_4__new (v_SIZE: usize) (value: t_Array u8 v_SIZE) =
  { f_value = value } <: t_MLDSASignature v_SIZE

let impl__as_ref (v_SIZE: usize) (self: t_MLDSASigningKey v_SIZE) = self.f_value

let impl__new (v_SIZE: usize) (value: t_Array u8 v_SIZE) =
  { f_value = value } <: t_MLDSASigningKey v_SIZE

let impl_2__as_ref (v_SIZE: usize) (self: t_MLDSAVerificationKey v_SIZE) = self.f_value

let impl_2__new (v_SIZE: usize) (value: t_Array u8 v_SIZE) =
  { f_value = value } <: t_MLDSAVerificationKey v_SIZE

let t_SigningError_cast_to_repr (x: t_SigningError) =
  match x <: t_SigningError with
  | SigningError_RejectionSamplingError  -> isz 0
  | SigningError_ContextTooLongError  -> isz 1

let t_VerificationError_cast_to_repr (x: t_VerificationError) =
  match x <: t_VerificationError with
  | VerificationError_MalformedHintError  -> isz 0
  | VerificationError_SignerResponseExceedsBoundError  -> isz 1
  | VerificationError_CommitmentHashesDontMatchError  -> isz 3
  | VerificationError_VerificationContextTooLongError  -> isz 6

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': v_SIZE: usize -> Core.Clone.t_Clone (t_MLDSASigningKey v_SIZE)

let impl_1 (v_SIZE: usize) = impl_1' v_SIZE

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': v_SIZE: usize -> Core.Clone.t_Clone (t_MLDSAVerificationKey v_SIZE)

let impl_3 (v_SIZE: usize) = impl_3' v_SIZE

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_5': v_SIZE: usize -> Core.Clone.t_Clone (t_MLDSASignature v_SIZE)

let impl_5 (v_SIZE: usize) = impl_5' v_SIZE

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_6': Core.Fmt.t_Debug t_VerificationError

let impl_6 = impl_6'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_7': Core.Fmt.t_Debug t_SigningError

let impl_7 = impl_7'

let impl__zero (v_SIZE: usize) (_: Prims.unit) =
  { f_value = Rust_primitives.Hax.repeat 0uy v_SIZE } <: t_MLDSASigningKey v_SIZE

let impl_2__zero (v_SIZE: usize) (_: Prims.unit) =
  { f_value = Rust_primitives.Hax.repeat 0uy v_SIZE } <: t_MLDSAVerificationKey v_SIZE

let impl_4__zero (v_SIZE: usize) (_: Prims.unit) =
  { f_value = Rust_primitives.Hax.repeat 0uy v_SIZE } <: t_MLDSASignature v_SIZE

let impl__as_slice (v_SIZE: usize) (self: t_MLDSASigningKey v_SIZE) = self.f_value <: t_Slice u8

let impl_2__as_slice (v_SIZE: usize) (self: t_MLDSAVerificationKey v_SIZE) =
  self.f_value <: t_Slice u8

let impl_4__as_slice (v_SIZE: usize) (self: t_MLDSASignature v_SIZE) = self.f_value <: t_Slice u8
