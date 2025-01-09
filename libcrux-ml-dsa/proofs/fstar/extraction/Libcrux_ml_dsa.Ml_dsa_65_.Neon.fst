module Libcrux_ml_dsa.Ml_dsa_65_.Neon
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let generate_key_pair (randomness: t_Array u8 (sz 32)) =
  let signing_key:t_Array u8 (sz 4032) = Rust_primitives.Hax.repeat 0uy (sz 4032) in
  let verification_key:t_Array u8 (sz 1952) = Rust_primitives.Hax.repeat 0uy (sz 1952) in
  let tmp0, tmp1:(t_Array u8 (sz 4032) & t_Array u8 (sz 1952)) =
    Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.Ml_dsa_65_.generate_key_pair randomness
      signing_key
      verification_key
  in
  let signing_key:t_Array u8 (sz 4032) = tmp0 in
  let verification_key:t_Array u8 (sz 1952) = tmp1 in
  let _:Prims.unit = () in
  {
    Libcrux_ml_dsa.Types.f_signing_key = Libcrux_ml_dsa.Types.impl__new (sz 4032) signing_key;
    Libcrux_ml_dsa.Types.f_verification_key
    =
    Libcrux_ml_dsa.Types.impl_2__new (sz 1952) verification_key
  }
  <:
  Libcrux_ml_dsa.Types.t_MLDSAKeyPair (sz 1952) (sz 4032)

let generate_key_pair_mut
      (randomness: t_Array u8 (sz 32))
      (signing_key: t_Array u8 (sz 4032))
      (verification_key: t_Array u8 (sz 1952))
     =
  let tmp0, tmp1:(t_Array u8 (sz 4032) & t_Array u8 (sz 1952)) =
    Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.Ml_dsa_65_.generate_key_pair randomness
      signing_key
      verification_key
  in
  let signing_key:t_Array u8 (sz 4032) = tmp0 in
  let verification_key:t_Array u8 (sz 1952) = tmp1 in
  let _:Prims.unit = () in
  signing_key, verification_key <: (t_Array u8 (sz 4032) & t_Array u8 (sz 1952))

let sign
      (signing_key: Libcrux_ml_dsa.Types.t_MLDSASigningKey (sz 4032))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
     =
  Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.Ml_dsa_65_.sign (Libcrux_ml_dsa.Types.impl__as_ref
        (sz 4032)
        signing_key
      <:
      t_Array u8 (sz 4032))
    message
    context
    randomness

let sign_mut
      (signing_key: t_Array u8 (sz 4032))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
      (signature: t_Array u8 (sz 3309))
     =
  let tmp0, out:(t_Array u8 (sz 3309) &
    Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_SigningError) =
    Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.Ml_dsa_65_.sign_mut signing_key
      message
      context
      randomness
      signature
  in
  let signature:t_Array u8 (sz 3309) = tmp0 in
  let hax_temp_output:Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_SigningError = out in
  signature, hax_temp_output
  <:
  (t_Array u8 (sz 3309) & Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_SigningError)

let sign_pre_hashed_shake128
      (signing_key: Libcrux_ml_dsa.Types.t_MLDSASigningKey (sz 4032))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
     =
  let pre_hash_buffer:t_Array u8 (sz 256) = Rust_primitives.Hax.repeat 0uy (sz 256) in
  let tmp0, out:(t_Array u8 (sz 256) &
    Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (sz 3309))
      Libcrux_ml_dsa.Types.t_SigningError) =
    Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.Ml_dsa_65_.sign_pre_hashed_shake128 (Libcrux_ml_dsa.Types.impl__as_ref
          (sz 4032)
          signing_key
        <:
        t_Array u8 (sz 4032))
      message
      context
      pre_hash_buffer
      randomness
  in
  let pre_hash_buffer:t_Array u8 (sz 256) = tmp0 in
  out

let verify
      (verification_key: Libcrux_ml_dsa.Types.t_MLDSAVerificationKey (sz 1952))
      (message context: t_Slice u8)
      (signature: Libcrux_ml_dsa.Types.t_MLDSASignature (sz 3309))
     =
  Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.Ml_dsa_65_.verify (Libcrux_ml_dsa.Types.impl_2__as_ref
        (sz 1952)
        verification_key
      <:
      t_Array u8 (sz 1952))
    message
    context
    (Libcrux_ml_dsa.Types.impl_4__as_ref (sz 3309) signature <: t_Array u8 (sz 3309))

let verify_pre_hashed_shake128
      (verification_key: Libcrux_ml_dsa.Types.t_MLDSAVerificationKey (sz 1952))
      (message context: t_Slice u8)
      (signature: Libcrux_ml_dsa.Types.t_MLDSASignature (sz 3309))
     =
  let pre_hash_buffer:t_Array u8 (sz 256) = Rust_primitives.Hax.repeat 0uy (sz 256) in
  let tmp0, out:(t_Array u8 (sz 256) &
    Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError) =
    Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.Ml_dsa_65_.verify_pre_hashed_shake128 (Libcrux_ml_dsa.Types.impl_2__as_ref
          (sz 1952)
          verification_key
        <:
        t_Array u8 (sz 1952))
      message
      context
      pre_hash_buffer
      (Libcrux_ml_dsa.Types.impl_4__as_ref (sz 3309) signature <: t_Array u8 (sz 3309))
  in
  let pre_hash_buffer:t_Array u8 (sz 256) = tmp0 in
  out
