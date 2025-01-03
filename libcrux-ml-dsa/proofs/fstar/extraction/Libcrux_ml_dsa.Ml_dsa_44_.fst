module Libcrux_ml_dsa.Ml_dsa_44_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let generate_key_pair (randomness: t_Array u8 (sz 32)) =
  let signing_key:t_Array u8 (sz 2560) = Rust_primitives.Hax.repeat 0uy (sz 2560) in
  let verification_key:t_Array u8 (sz 1312) = Rust_primitives.Hax.repeat 0uy (sz 1312) in
  let tmp0, tmp1:(t_Array u8 (sz 2560) & t_Array u8 (sz 1312)) =
    Libcrux_ml_dsa.Ml_dsa_generic.Multiplexing.generate_key_pair_v44 randomness
      signing_key
      verification_key
  in
  let signing_key:t_Array u8 (sz 2560) = tmp0 in
  let verification_key:t_Array u8 (sz 1312) = tmp1 in
  let _:Prims.unit = () in
  {
    Libcrux_ml_dsa.Types.f_signing_key = Libcrux_ml_dsa.Types.impl__new (sz 2560) signing_key;
    Libcrux_ml_dsa.Types.f_verification_key
    =
    Libcrux_ml_dsa.Types.impl_2__new (sz 1312) verification_key
  }
  <:
  Libcrux_ml_dsa.Types.t_MLDSAKeyPair (sz 1312) (sz 2560)

let sign
      (signing_key: Libcrux_ml_dsa.Types.t_MLDSASigningKey (sz 2560))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
     =
  Libcrux_ml_dsa.Ml_dsa_generic.Multiplexing.sign (sz 4) (sz 4) (sz 16) (sz 2) (sz 96) (sz 17)
    95232l (sz 192) (sz 768) (sz 32) (sz 39) (sz 80) (sz 576) (sz 2560) (sz 2420)
    (Libcrux_ml_dsa.Types.impl__as_ref (sz 2560) signing_key <: t_Array u8 (sz 2560)) message
    context randomness

let sign_pre_hashed_shake128
      (signing_key: Libcrux_ml_dsa.Types.t_MLDSASigningKey (sz 2560))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
     =
  Libcrux_ml_dsa.Ml_dsa_generic.Multiplexing.sign_pre_hashed_shake128 (sz 4) (sz 4) (sz 16) (sz 2)
    (sz 96) (sz 17) 95232l (sz 192) (sz 768) (sz 32) (sz 39) (sz 80) (sz 576) (sz 2560) (sz 2420)
    (Libcrux_ml_dsa.Types.impl__as_ref (sz 2560) signing_key <: t_Array u8 (sz 2560)) message
    context randomness

let verify
      (verification_key: Libcrux_ml_dsa.Types.t_MLDSAVerificationKey (sz 1312))
      (message context: t_Slice u8)
      (signature: Libcrux_ml_dsa.Types.t_MLDSASignature (sz 2420))
     =
  Libcrux_ml_dsa.Ml_dsa_generic.Multiplexing.verify (sz 4) (sz 4) (sz 16) (sz 2420) (sz 1312)
    (sz 17) (sz 576) 95232l 78l (sz 192) (sz 768) (sz 32) (sz 39) (sz 80)
    (Libcrux_ml_dsa.Types.impl_2__as_ref (sz 1312) verification_key <: t_Array u8 (sz 1312)) message
    context (Libcrux_ml_dsa.Types.impl_4__as_ref (sz 2420) signature <: t_Array u8 (sz 2420))

let verify_pre_hashed_shake128
      (verification_key: Libcrux_ml_dsa.Types.t_MLDSAVerificationKey (sz 1312))
      (message context: t_Slice u8)
      (signature: Libcrux_ml_dsa.Types.t_MLDSASignature (sz 2420))
     =
  Libcrux_ml_dsa.Ml_dsa_generic.Multiplexing.verify_pre_hashed_shake128 (sz 4) (sz 4) (sz 16)
    (sz 2420) (sz 1312) (sz 17) (sz 576) 95232l 78l (sz 192) (sz 768) (sz 32) (sz 39) (sz 80)
    (Libcrux_ml_dsa.Types.impl_2__as_ref (sz 1312) verification_key <: t_Array u8 (sz 1312)) message
    context (Libcrux_ml_dsa.Types.impl_4__as_ref (sz 2420) signature <: t_Array u8 (sz 2420))
