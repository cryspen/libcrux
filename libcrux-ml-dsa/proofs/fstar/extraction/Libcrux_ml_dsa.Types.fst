module Libcrux_ml_dsa.Types
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// The number of bytes
let impl__len (v_SIZE: usize) (_: Prims.unit) : usize = v_SIZE

/// The number of bytes
let impl_2__len (v_SIZE: usize) (_: Prims.unit) : usize = v_SIZE

/// The number of bytes
let impl_4__len (v_SIZE: usize) (_: Prims.unit) : usize = v_SIZE

///An ML-DSA signature.
type t_MLDSASignature (v_SIZE: usize) =
  | MLDSASignature : t_Array u8 v_SIZE -> t_MLDSASignature v_SIZE

/// A reference to the raw byte slice.
let impl_4__as_slice (v_SIZE: usize) (self: t_MLDSASignature v_SIZE) : t_Slice u8 =
  self._0 <: t_Slice u8

///An ML-DSA signature key.
type t_MLDSASigningKey (v_SIZE: usize) =
  | MLDSASigningKey : t_Array u8 v_SIZE -> t_MLDSASigningKey v_SIZE

/// A reference to the raw byte slice.
let impl__as_slice (v_SIZE: usize) (self: t_MLDSASigningKey v_SIZE) : t_Slice u8 =
  self._0 <: t_Slice u8

///An ML-DSA verification key.
type t_MLDSAVerificationKey (v_SIZE: usize) =
  | MLDSAVerificationKey : t_Array u8 v_SIZE -> t_MLDSAVerificationKey v_SIZE

/// A reference to the raw byte slice.
let impl_2__as_slice (v_SIZE: usize) (self: t_MLDSAVerificationKey v_SIZE) : t_Slice u8 =
  self._0 <: t_Slice u8

/// An ML-DSA key pair.
type t_MLDSAKeyPair (v_VERIFICATION_KEY_SIZE: usize) (v_SIGNING_KEY_SIZE: usize) = {
  f_signing_key:t_MLDSASigningKey v_SIGNING_KEY_SIZE;
  f_verification_key:t_MLDSAVerificationKey v_VERIFICATION_KEY_SIZE
}
