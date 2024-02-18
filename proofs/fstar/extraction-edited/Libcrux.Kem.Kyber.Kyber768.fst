module Libcrux.Kem.Kyber.Kyber768
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let decapsulate
      (secret_key: Libcrux.Kem.Kyber.Types.t_MlKemPrivateKey (sz 2400))
      (ciphertext: Libcrux.Kem.Kyber.Types.t_MlKemCiphertext (sz 1088))
     =
    Libcrux.Kem.Kyber.decapsulate #Spec.Kyber.kyber768_params (sz 3) (sz 2400) (sz 1152) (sz 1184) (sz 1088) (sz 1152) (sz 960)
    (sz 128) (sz 10) (sz 4) (sz 320) (sz 2) (sz 128) (sz 2) (sz 128) (sz 1120) secret_key ciphertext

let encapsulate
      (public_key: Libcrux.Kem.Kyber.Types.t_MlKemPublicKey (sz 1184))
      (randomness: t_Array u8 (sz 32))
     =
  Libcrux.Kem.Kyber.encapsulate #Spec.Kyber.kyber768_params (sz 3) (sz 1088) (sz 1184) (sz 1152) (sz 960) (sz 128) (sz 10)
    (sz 4) (sz 320) (sz 2) (sz 128) (sz 2) (sz 128) public_key randomness

let validate_public_key (public_key: Libcrux.Kem.Kyber.Types.t_MlKemPublicKey (sz 1184)) =
  if
    Libcrux.Kem.Kyber.validate_public_key #Spec.Kyber.kyber768_params (sz 3)
      (sz 1152)
      (sz 1184)
      public_key.Libcrux.Kem.Kyber.Types.f_value
  then
    Core.Option.Option_Some public_key
    <:
    Core.Option.t_Option (Libcrux.Kem.Kyber.Types.t_MlKemPublicKey (sz 1184))
  else
    Core.Option.Option_None
    <:
    Core.Option.t_Option (Libcrux.Kem.Kyber.Types.t_MlKemPublicKey (sz 1184))

let generate_key_pair (randomness: t_Array u8 (sz 64)) =
  Libcrux.Kem.Kyber.generate_keypair #Spec.Kyber.kyber768_params (sz 3)
    (sz 1152)
    (sz 2400)
    (sz 1184)
    (sz 1152)
    (sz 2)
    (sz 128)
    randomness
