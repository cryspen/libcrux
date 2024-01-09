module Libcrux.Kem.Kyber.Kyber1024
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let decapsulate_1024_
      (secret_key: Libcrux.Kem.Kyber.Types.t_KyberPrivateKey (sz 3168))
      (ciphertext: Libcrux.Kem.Kyber.Types.t_KyberCiphertext (sz 1568))
     =
  Libcrux.Kem.Kyber.decapsulate (sz 4) (sz 3168) (sz 1536) (sz 1568) (sz 1568) (sz 1536) (sz 1408)
    (sz 160) (sz 11) (sz 5) (sz 352) (sz 2) (sz 128) (sz 2) (sz 128) (sz 1600) secret_key ciphertext

let encapsulate_1024_
      (public_key: Libcrux.Kem.Kyber.Types.t_KyberPublicKey (sz 1568))
      (randomness: t_Array u8 (sz 32))
     =
  Libcrux.Kem.Kyber.encapsulate (sz 4) (sz 1568) (sz 1568) (sz 1536) (sz 1408) (sz 160) (sz 11)
    (sz 5) (sz 352) (sz 2) (sz 128) (sz 2) (sz 128) public_key randomness

let generate_key_pair_1024_ (randomness: t_Array u8 (sz 64)) =
  Libcrux.Kem.Kyber.generate_keypair (sz 4)
    (sz 1536)
    (sz 3168)
    (sz 1568)
    (sz 1536)
    (sz 2)
    (sz 128)
    randomness
