module Libcrux.Kem.Kyber.Kyber1024
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let decapsulate
      (secret_key: Libcrux.Kem.Kyber.Types.t_MlKemPrivateKey (sz 3168))
      (ciphertext: Libcrux.Kem.Kyber.Types.t_MlKemCiphertext (sz 1568))
     =
  Libcrux.Kem.Kyber.decapsulate #Spec.Kyber.kyber1024_params (sz 4) (sz 3168) (sz 1536) (sz 1568) (sz 1568) (sz 1536) (sz 1408)
    (sz 160) (sz 11) (sz 5) (sz 352) (sz 2) (sz 128) (sz 2) (sz 128) (sz 1600) secret_key ciphertext

let encapsulate
      (public_key: Libcrux.Kem.Kyber.Types.t_MlKemPublicKey (sz 1568))
      (randomness: t_Array u8 (sz 32))
     =
  Libcrux.Kem.Kyber.encapsulate #Spec.Kyber.kyber1024_params (sz 4) (sz 1568) (sz 1568) (sz 1536) (sz 1408) (sz 160) (sz 11)
    (sz 5) (sz 352) (sz 2) (sz 128) (sz 2) (sz 128) public_key randomness

let validate_public_key (public_key: Libcrux.Kem.Kyber.Types.t_MlKemPublicKey (sz 1568)) =
  if
    Libcrux.Kem.Kyber.validate_public_key #Spec.Kyber.kyber1024_params (sz 4)
      (sz 1536)
      (sz 1568)
      public_key.Libcrux.Kem.Kyber.Types.f_value
  then
    Core.Option.Option_Some public_key
    <:
    Core.Option.t_Option (Libcrux.Kem.Kyber.Types.t_MlKemPublicKey (sz 1568))
  else
    Core.Option.Option_None
    <:
    Core.Option.t_Option (Libcrux.Kem.Kyber.Types.t_MlKemPublicKey (sz 1568))

let generate_key_pair (randomness: t_Array u8 (sz 64)) =
  Libcrux.Kem.Kyber.generate_keypair #Spec.Kyber.kyber1024_params (sz 4)
    (sz 1536)
    (sz 3168)
    (sz 1568)
    (sz 1536)
    (sz 2)
    (sz 128)
    randomness
