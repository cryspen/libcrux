module Libcrux_ml_kem.Kyber512
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let decapsulate
      (secret_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (sz 1632))
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (sz 768))
     =
  Libcrux_ml_kem.decapsulate (sz 2) (sz 1632) (sz 768) (sz 800) (sz 768) (sz 768) (sz 640) (sz 128)
    (sz 10) (sz 4) (sz 320) (sz 3) (sz 192) (sz 2) (sz 128) (sz 800) secret_key ciphertext

let encapsulate
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 800))
      (randomness: t_Array u8 (sz 32))
     =
  Libcrux_ml_kem.encapsulate (sz 2) (sz 768) (sz 800) (sz 768) (sz 640) (sz 128) (sz 10) (sz 4)
    (sz 320) (sz 3) (sz 192) (sz 2) (sz 128) public_key randomness

let validate_public_key (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 800)) =
  if
    Libcrux_ml_kem.validate_public_key (sz 2)
      (sz 768)
      (sz 800)
      public_key.Libcrux_ml_kem.Types.f_value
  then
    Core.Option.Option_Some public_key
    <:
    Core.Option.t_Option (Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 800))
  else
    Core.Option.Option_None <: Core.Option.t_Option (Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 800))

let generate_key_pair (randomness: t_Array u8 (sz 64)) =
  Libcrux_ml_kem.generate_keypair (sz 2)
    (sz 768)
    (sz 1632)
    (sz 800)
    (sz 768)
    (sz 3)
    (sz 192)
    randomness
