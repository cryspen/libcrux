module Libcrux_ml_dsa.Ml_dsa_87_.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let generate_key_pair (randomness: t_Array u8 (sz 32)) =
  let signing_key, verification_key:(t_Array u8 (sz 4896) & t_Array u8 (sz 2592)) =
    Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.generate_key_pair (sz 8)
      (sz 7)
      (sz 2)
      (sz 96)
      (sz 4896)
      (sz 2592)
      randomness
  in
  {
    Libcrux_ml_dsa.Types.f_signing_key
    =
    Libcrux_ml_dsa.Types.MLDSASigningKey signing_key
    <:
    Libcrux_ml_dsa.Types.t_MLDSASigningKey (sz 4896);
    Libcrux_ml_dsa.Types.f_verification_key
    =
    Libcrux_ml_dsa.Types.MLDSAVerificationKey verification_key
    <:
    Libcrux_ml_dsa.Types.t_MLDSAVerificationKey (sz 2592)
  }
  <:
  Libcrux_ml_dsa.Types.t_MLDSAKeyPair (sz 2592) (sz 4896)

let sign
      (signing_key: Libcrux_ml_dsa.Types.t_MLDSASigningKey (sz 4896))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
     =
  Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.sign (sz 8) (sz 7) (sz 2) (sz 96) (sz 19)
    261888l (sz 128) (sz 1024) (sz 64) (sz 60) (sz 75) (sz 640) (sz 4896) (sz 4627)
    signing_key.Libcrux_ml_dsa.Types._0 message context randomness

let sign_pre_hashed_shake128
      (signing_key: Libcrux_ml_dsa.Types.t_MLDSASigningKey (sz 4896))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
     =
  Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.sign_pre_hashed_shake128 (sz 8) (sz 7)
    (sz 2) (sz 96) (sz 19) 261888l (sz 128) (sz 1024) (sz 64) (sz 60) (sz 75) (sz 640) (sz 4896)
    (sz 4627) signing_key.Libcrux_ml_dsa.Types._0 message context randomness

let verify
      (verification_key: Libcrux_ml_dsa.Types.t_MLDSAVerificationKey (sz 2592))
      (message context: t_Slice u8)
      (signature: Libcrux_ml_dsa.Types.t_MLDSASignature (sz 4627))
     =
  Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.verify (sz 8) (sz 7) (sz 4627) (sz 2592)
    (sz 19) (sz 640) 261888l 120l (sz 128) (sz 1024) (sz 64) (sz 60) (sz 75)
    verification_key.Libcrux_ml_dsa.Types._0 message context signature.Libcrux_ml_dsa.Types._0

let verify_pre_hashed_shake128
      (verification_key: Libcrux_ml_dsa.Types.t_MLDSAVerificationKey (sz 2592))
      (message context: t_Slice u8)
      (signature: Libcrux_ml_dsa.Types.t_MLDSASignature (sz 4627))
     =
  Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.verify_pre_hashed_shake128 (sz 8) (sz 7)
    (sz 4627) (sz 2592) (sz 19) (sz 640) 261888l 120l (sz 128) (sz 1024) (sz 64) (sz 60) (sz 75)
    verification_key.Libcrux_ml_dsa.Types._0 message context signature.Libcrux_ml_dsa.Types._0
