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
