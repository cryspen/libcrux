module Libcrux.Kem.Kyber.Kyber768
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let decapsulate_768_
      (secret_key: Libcrux.Kem.Kyber.Types.t_KyberPrivateKey (sz 2400))
      (ciphertext: Libcrux.Kem.Kyber.Types.t_KyberCiphertext (sz 1088))
     =
  Libcrux.Kem.Kyber.decapsulate (sz 3) (sz 2400) (sz 1152) (sz 1184) (sz 1088) (sz 1152) (sz 960)
    (sz 128) (sz 10) (sz 4) (sz 320) (sz 2) (sz 128) (sz 2) (sz 128) (sz 1120) secret_key ciphertext

let encapsulate_768_
      (public_key: Libcrux.Kem.Kyber.Types.t_KyberPublicKey (sz 1184))
      (randomness: t_Array u8 (sz 32))
     =
  Libcrux.Kem.Kyber.encapsulate (sz 3) (sz 1088) (sz 1184) (sz 1152) (sz 960) (sz 128) (sz 10)
    (sz 4) (sz 320) (sz 2) (sz 128) (sz 2) (sz 128) public_key randomness

let generate_key_pair_768_ (randomness: t_Array u8 (sz 64)) =
  Libcrux.Kem.Kyber.generate_keypair (sz 3)
    (sz 1152)
    (sz 2400)
    (sz 1184)
    (sz 1152)
    (sz 2)
    (sz 128)
    randomness
