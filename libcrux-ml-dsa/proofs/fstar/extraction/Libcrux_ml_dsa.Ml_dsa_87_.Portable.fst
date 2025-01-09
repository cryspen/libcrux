module Libcrux_ml_dsa.Ml_dsa_87_.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let generate_key_pair (randomness: t_Array u8 (sz 32)) =
  let signing_key:t_Array u8 (sz 4896) = Rust_primitives.Hax.repeat 0uy (sz 4896) in
  let verification_key:t_Array u8 (sz 2592) = Rust_primitives.Hax.repeat 0uy (sz 2592) in
  let tmp0, tmp1:(t_Array u8 (sz 4896) & t_Array u8 (sz 2592)) =
    Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.Ml_dsa_87_.generate_key_pair randomness
      signing_key
      verification_key
  in
  let signing_key:t_Array u8 (sz 4896) = tmp0 in
  let verification_key:t_Array u8 (sz 2592) = tmp1 in
  let _:Prims.unit = () in
  {
    Libcrux_ml_dsa.Types.f_signing_key = Libcrux_ml_dsa.Types.impl__new (sz 4896) signing_key;
    Libcrux_ml_dsa.Types.f_verification_key
    =
    Libcrux_ml_dsa.Types.impl_2__new (sz 2592) verification_key
  }
  <:
  Libcrux_ml_dsa.Types.t_MLDSAKeyPair (sz 2592) (sz 4896)

let sign
      (signing_key: Libcrux_ml_dsa.Types.t_MLDSASigningKey (sz 4896))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
     =
  Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.Ml_dsa_87_.sign (Libcrux_ml_dsa.Types.impl__as_ref
        (sz 4896)
        signing_key
      <:
      t_Array u8 (sz 4896))
    message
    context
    randomness

let sign_mut
      (signing_key: Libcrux_ml_dsa.Types.t_MLDSASigningKey (sz 4896))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
      (signature: t_Array u8 (sz 4627))
     =
  let tmp0, out:(t_Array u8 (sz 4627) &
    Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_SigningError) =
    Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.Ml_dsa_87_.sign_mut (Libcrux_ml_dsa.Types.impl__as_ref
          (sz 4896)
          signing_key
        <:
        t_Array u8 (sz 4896))
      message
      context
      randomness
      signature
  in
  let signature:t_Array u8 (sz 4627) = tmp0 in
  let hax_temp_output:Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_SigningError = out in
  signature, hax_temp_output
  <:
  (t_Array u8 (sz 4627) & Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_SigningError)

let sign_pre_hashed_shake128
      (signing_key: Libcrux_ml_dsa.Types.t_MLDSASigningKey (sz 4896))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
     =
  let pre_hash_buffer:t_Array u8 (sz 256) = Rust_primitives.Hax.repeat 0uy (sz 256) in
  let tmp0, out:(t_Array u8 (sz 256) &
    Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (sz 4627))
      Libcrux_ml_dsa.Types.t_SigningError) =
    Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.Ml_dsa_87_.sign_pre_hashed_shake128 (Libcrux_ml_dsa.Types.impl__as_ref
          (sz 4896)
          signing_key
        <:
        t_Array u8 (sz 4896))
      message
      context
      pre_hash_buffer
      randomness
  in
  let pre_hash_buffer:t_Array u8 (sz 256) = tmp0 in
  out

let verify
      (verification_key: Libcrux_ml_dsa.Types.t_MLDSAVerificationKey (sz 2592))
      (message context: t_Slice u8)
      (signature: Libcrux_ml_dsa.Types.t_MLDSASignature (sz 4627))
     =
  Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.Ml_dsa_87_.verify (Libcrux_ml_dsa.Types.impl_2__as_ref
        (sz 2592)
        verification_key
      <:
      t_Array u8 (sz 2592))
    message
    context
    (Libcrux_ml_dsa.Types.impl_4__as_ref (sz 4627) signature <: t_Array u8 (sz 4627))

let verify_pre_hashed_shake128
      (verification_key: Libcrux_ml_dsa.Types.t_MLDSAVerificationKey (sz 2592))
      (message context: t_Slice u8)
      (signature: Libcrux_ml_dsa.Types.t_MLDSASignature (sz 4627))
     =
  let pre_hash_buffer:t_Array u8 (sz 256) = Rust_primitives.Hax.repeat 0uy (sz 256) in
  let tmp0, out:(t_Array u8 (sz 256) &
    Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError) =
    Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.Ml_dsa_87_.verify_pre_hashed_shake128 (Libcrux_ml_dsa.Types.impl_2__as_ref
          (sz 2592)
          verification_key
        <:
        t_Array u8 (sz 2592))
      message
      context
      pre_hash_buffer
      (Libcrux_ml_dsa.Types.impl_4__as_ref (sz 4627) signature <: t_Array u8 (sz 4627))
  in
  let pre_hash_buffer:t_Array u8 (sz 256) = tmp0 in
  out
