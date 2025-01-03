module Libcrux_ml_dsa.Ml_dsa_87_.Neon
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let generate_key_pair (randomness: t_Array u8 (sz 32)) =
  let signing_key:t_Array u8 (sz 4896) = Rust_primitives.Hax.repeat 0uy (sz 4896) in
  let verification_key:t_Array u8 (sz 2592) = Rust_primitives.Hax.repeat 0uy (sz 2592) in
  let tmp0, tmp1:(t_Array u8 (sz 4896) & t_Array u8 (sz 2592)) =
    Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.generate_key_pair_v87 randomness
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
  Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.sign (sz 8) (sz 7) (sz 56) (sz 2) (sz 96)
    (sz 19) 261888l (sz 128) (sz 1024) (sz 64) (sz 60) (sz 75) (sz 640) (sz 4896) (sz 4627)
    (Libcrux_ml_dsa.Types.impl__as_ref (sz 4896) signing_key <: t_Array u8 (sz 4896)) message
    context randomness

let sign_pre_hashed_shake128
      (signing_key: Libcrux_ml_dsa.Types.t_MLDSASigningKey (sz 4896))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
     =
  Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.sign_pre_hashed_shake128 (sz 8) (sz 7) (sz 56)
    (sz 2) (sz 96) (sz 19) 261888l (sz 128) (sz 1024) (sz 64) (sz 60) (sz 75) (sz 640) (sz 4896)
    (sz 4627) (Libcrux_ml_dsa.Types.impl__as_ref (sz 4896) signing_key <: t_Array u8 (sz 4896))
    message context randomness

let verify
      (verification_key: Libcrux_ml_dsa.Types.t_MLDSAVerificationKey (sz 2592))
      (message context: t_Slice u8)
      (signature: Libcrux_ml_dsa.Types.t_MLDSASignature (sz 4627))
     =
  Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.verify (sz 8) (sz 7) (sz 56) (sz 4627) (sz 2592)
    (sz 19) (sz 640) 261888l 120l (sz 128) (sz 1024) (sz 64) (sz 60) (sz 75)
    (Libcrux_ml_dsa.Types.impl_2__as_ref (sz 2592) verification_key <: t_Array u8 (sz 2592)) message
    context (Libcrux_ml_dsa.Types.impl_4__as_ref (sz 4627) signature <: t_Array u8 (sz 4627))

let verify_pre_hashed_shake128
      (verification_key: Libcrux_ml_dsa.Types.t_MLDSAVerificationKey (sz 2592))
      (message context: t_Slice u8)
      (signature: Libcrux_ml_dsa.Types.t_MLDSASignature (sz 4627))
     =
  Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.verify_pre_hashed_shake128 (sz 8) (sz 7) (sz 56)
    (sz 4627) (sz 2592) (sz 19) (sz 640) 261888l 120l (sz 128) (sz 1024) (sz 64) (sz 60) (sz 75)
    (Libcrux_ml_dsa.Types.impl_2__as_ref (sz 2592) verification_key <: t_Array u8 (sz 2592)) message
    context (Libcrux_ml_dsa.Types.impl_4__as_ref (sz 4627) signature <: t_Array u8 (sz 4627))
