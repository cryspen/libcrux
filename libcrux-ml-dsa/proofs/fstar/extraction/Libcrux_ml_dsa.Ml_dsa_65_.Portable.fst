module Libcrux_ml_dsa.Ml_dsa_65_.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let generate_key_pair (randomness: t_Array u8 (sz 32)) =
  let signing_key, verification_key:(t_Array u8 (sz 4032) & t_Array u8 (sz 1952)) =
    Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.generate_key_pair (sz 6)
      (sz 5)
      (sz 4)
      (sz 128)
      (sz 4032)
      (sz 1952)
      randomness
  in
  {
    Libcrux_ml_dsa.Types.f_signing_key = Libcrux_ml_dsa.Types.impl__new (sz 4032) signing_key;
    Libcrux_ml_dsa.Types.f_verification_key
    =
    Libcrux_ml_dsa.Types.impl_2__new (sz 1952) verification_key
  }
  <:
  Libcrux_ml_dsa.Types.t_MLDSAKeyPair (sz 1952) (sz 4032)

let sign
      (signing_key: Libcrux_ml_dsa.Types.t_MLDSASigningKey (sz 4032))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
     =
  Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.sign (sz 6) (sz 5) (sz 4) (sz 128) (sz 19)
    261888l (sz 128) (sz 768) (sz 48) (sz 49) (sz 55) (sz 640) (sz 4032) (sz 3309)
    (Libcrux_ml_dsa.Types.impl__as_raw (sz 4032) signing_key <: t_Array u8 (sz 4032)) message
    context randomness

let sign_pre_hashed_shake128
      (signing_key: Libcrux_ml_dsa.Types.t_MLDSASigningKey (sz 4032))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
     =
  Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.sign_pre_hashed_shake128 (sz 6) (sz 5)
    (sz 4) (sz 128) (sz 19) 261888l (sz 128) (sz 768) (sz 48) (sz 49) (sz 55) (sz 640) (sz 4032)
    (sz 3309) (Libcrux_ml_dsa.Types.impl__as_raw (sz 4032) signing_key <: t_Array u8 (sz 4032))
    message context randomness

let verify
      (verification_key: Libcrux_ml_dsa.Types.t_MLDSAVerificationKey (sz 1952))
      (message context: t_Slice u8)
      (signature: Libcrux_ml_dsa.Types.t_MLDSASignature (sz 3309))
     =
  Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.verify (sz 6) (sz 5) (sz 3309) (sz 1952)
    (sz 19) (sz 640) 261888l 196l (sz 128) (sz 768) (sz 48) (sz 49) (sz 55)
    (Libcrux_ml_dsa.Types.impl_2__as_raw (sz 1952) verification_key <: t_Array u8 (sz 1952)) message
    context (Libcrux_ml_dsa.Types.impl_4__as_raw (sz 3309) signature <: t_Array u8 (sz 3309))

let verify_pre_hashed_shake128
      (verification_key: Libcrux_ml_dsa.Types.t_MLDSAVerificationKey (sz 1952))
      (message context: t_Slice u8)
      (signature: Libcrux_ml_dsa.Types.t_MLDSASignature (sz 3309))
     =
  Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.verify_pre_hashed_shake128 (sz 6) (sz 5)
    (sz 3309) (sz 1952) (sz 19) (sz 640) 261888l 196l (sz 128) (sz 768) (sz 48) (sz 49) (sz 55)
    (Libcrux_ml_dsa.Types.impl_2__as_raw (sz 1952) verification_key <: t_Array u8 (sz 1952)) message
    context (Libcrux_ml_dsa.Types.impl_4__as_raw (sz 3309) signature <: t_Array u8 (sz 3309))
