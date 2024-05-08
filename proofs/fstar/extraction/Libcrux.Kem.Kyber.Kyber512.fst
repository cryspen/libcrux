module Libcrux.Kem.Kyber.Kyber512
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let decapsulate
      (secret_key: Libcrux.Kem.Kyber.Types.t_MlKemPrivateKey (sz 1632))
      (ciphertext: Libcrux.Kem.Kyber.Types.t_MlKemCiphertext (sz 768))
     =
  Libcrux.Kem.Kyber.decapsulate (sz 2) (sz 1632) (sz 768) (sz 800) (sz 768) (sz 768) (sz 640)
    (sz 128) (sz 10) (sz 4) (sz 320) (sz 3) (sz 192) (sz 2) (sz 128) (sz 800) secret_key ciphertext

let encapsulate
      (public_key: Libcrux.Kem.Kyber.Types.t_MlKemPublicKey (sz 800))
      (randomness: t_Array u8 (sz 32))
     =
  Libcrux.Kem.Kyber.encapsulate (sz 2) (sz 768) (sz 800) (sz 768) (sz 640) (sz 128) (sz 10) (sz 4)
    (sz 320) (sz 3) (sz 192) (sz 2) (sz 128) public_key randomness

let validate_public_key (public_key: Libcrux.Kem.Kyber.Types.t_MlKemPublicKey (sz 800)) =
  if
    Libcrux.Kem.Kyber.validate_public_key (sz 2)
      (sz 768)
      (sz 800)
      public_key.Libcrux.Kem.Kyber.Types.f_value
  then
    Core.Option.Option_Some public_key
    <:
    Core.Option.t_Option (Libcrux.Kem.Kyber.Types.t_MlKemPublicKey (sz 800))
  else
    Core.Option.Option_None
    <:
    Core.Option.t_Option (Libcrux.Kem.Kyber.Types.t_MlKemPublicKey (sz 800))

let decapsulate_unpacked
      (state: Libcrux.Kem.Kyber.t_MlKemState (sz 2))
      (ciphertext: Libcrux.Kem.Kyber.Types.t_MlKemCiphertext (sz 768))
     =
  Libcrux.Kem.Kyber.decapsulate_unpacked (sz 2) (sz 1632) (sz 768) (sz 800) (sz 768) (sz 768)
    (sz 640) (sz 128) (sz 10) (sz 4) (sz 320) (sz 3) (sz 192) (sz 2) (sz 128) (sz 800) state
    ciphertext

let generate_key_pair (randomness: t_Array u8 (sz 64)) =
  Libcrux.Kem.Kyber.generate_keypair (sz 2)
    (sz 768)
    (sz 1632)
    (sz 800)
    (sz 768)
    (sz 3)
    (sz 192)
    randomness

let generate_key_pair_unpacked (randomness: t_Array u8 (sz 64)) =
  Libcrux.Kem.Kyber.generate_keypair_unpacked (sz 2)
    (sz 768)
    (sz 1632)
    (sz 800)
    (sz 768)
    (sz 3)
    (sz 192)
    randomness
