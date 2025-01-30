module Libcrux_ml_dsa.Ml_dsa_44_.Avx2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let generate_key_pair (randomness: t_Array u8 (mk_usize 32)) =
  let signing_key:t_Array u8 (mk_usize 2560) =
    Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 2560)
  in
  let verification_key:t_Array u8 (mk_usize 1312) =
    Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 1312)
  in
  let tmp0, tmp1:(t_Array u8 (mk_usize 2560) & t_Array u8 (mk_usize 1312)) =
    Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Avx2.Ml_dsa_44_.generate_key_pair randomness
      signing_key
      verification_key
  in
  let signing_key:t_Array u8 (mk_usize 2560) = tmp0 in
  let verification_key:t_Array u8 (mk_usize 1312) = tmp1 in
  let _:Prims.unit = () in
  {
    Libcrux_ml_dsa.Types.f_signing_key = Libcrux_ml_dsa.Types.impl__new (mk_usize 2560) signing_key;
    Libcrux_ml_dsa.Types.f_verification_key
    =
    Libcrux_ml_dsa.Types.impl_2__new (mk_usize 1312) verification_key
  }
  <:
  Libcrux_ml_dsa.Types.t_MLDSAKeyPair (mk_usize 1312) (mk_usize 2560)

let sign
      (signing_key: Libcrux_ml_dsa.Types.t_MLDSASigningKey (mk_usize 2560))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (mk_usize 32))
     =
  Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Avx2.Ml_dsa_44_.sign (Libcrux_ml_dsa.Types.impl__as_ref
        (mk_usize 2560)
        signing_key
      <:
      t_Array u8 (mk_usize 2560))
    message
    context
    randomness

let sign_mut
      (signing_key: Libcrux_ml_dsa.Types.t_MLDSASigningKey (mk_usize 2560))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (mk_usize 32))
      (signature: t_Array u8 (mk_usize 2420))
     =
  let tmp0, out:(t_Array u8 (mk_usize 2420) &
    Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_SigningError) =
    Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Avx2.Ml_dsa_44_.sign_mut (Libcrux_ml_dsa.Types.impl__as_ref
          (mk_usize 2560)
          signing_key
        <:
        t_Array u8 (mk_usize 2560))
      message
      context
      randomness
      signature
  in
  let signature:t_Array u8 (mk_usize 2420) = tmp0 in
  let hax_temp_output:Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_SigningError = out in
  signature, hax_temp_output
  <:
  (t_Array u8 (mk_usize 2420) & Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_SigningError)

let sign_pre_hashed_shake128
      (signing_key: Libcrux_ml_dsa.Types.t_MLDSASigningKey (mk_usize 2560))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (mk_usize 32))
     =
  let pre_hash_buffer:t_Array u8 (mk_usize 256) =
    Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 256)
  in
  let tmp0, out:(t_Array u8 (mk_usize 256) &
    Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (mk_usize 2420))
      Libcrux_ml_dsa.Types.t_SigningError) =
    Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Avx2.Ml_dsa_44_.sign_pre_hashed_shake128 (Libcrux_ml_dsa.Types.impl__as_ref
          (mk_usize 2560)
          signing_key
        <:
        t_Array u8 (mk_usize 2560))
      message
      context
      pre_hash_buffer
      randomness
  in
  let pre_hash_buffer:t_Array u8 (mk_usize 256) = tmp0 in
  out

let verify
      (verification_key: Libcrux_ml_dsa.Types.t_MLDSAVerificationKey (mk_usize 1312))
      (message context: t_Slice u8)
      (signature: Libcrux_ml_dsa.Types.t_MLDSASignature (mk_usize 2420))
     =
  Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Avx2.Ml_dsa_44_.verify (Libcrux_ml_dsa.Types.impl_2__as_ref
        (mk_usize 1312)
        verification_key
      <:
      t_Array u8 (mk_usize 1312))
    message
    context
    (Libcrux_ml_dsa.Types.impl_4__as_ref (mk_usize 2420) signature <: t_Array u8 (mk_usize 2420))

let verify_pre_hashed_shake128
      (verification_key: Libcrux_ml_dsa.Types.t_MLDSAVerificationKey (mk_usize 1312))
      (message context: t_Slice u8)
      (signature: Libcrux_ml_dsa.Types.t_MLDSASignature (mk_usize 2420))
     =
  let pre_hash_buffer:t_Array u8 (mk_usize 256) =
    Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 256)
  in
  let tmp0, out:(t_Array u8 (mk_usize 256) &
    Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError) =
    Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Avx2.Ml_dsa_44_.verify_pre_hashed_shake128 (Libcrux_ml_dsa.Types.impl_2__as_ref
          (mk_usize 1312)
          verification_key
        <:
        t_Array u8 (mk_usize 1312))
      message
      context
      pre_hash_buffer
      (Libcrux_ml_dsa.Types.impl_4__as_ref (mk_usize 2420) signature <: t_Array u8 (mk_usize 2420))
  in
  let pre_hash_buffer:t_Array u8 (mk_usize 256) = tmp0 in
  out
