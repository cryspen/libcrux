module Libcrux.Kem.Kyber.Kyber512
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let decapsulate_512_
      (secret_key: Libcrux.Kem.Kyber.Types.t_KyberPrivateKey (sz 1632))
      (ciphertext: Libcrux.Kem.Kyber.Types.t_KyberCiphertext (sz 768))
     =
  Libcrux.Kem.Kyber.decapsulate (sz 2) (sz 1632) (sz 768) (sz 800) (sz 768) (sz 768) (sz 640)
    (sz 128) (sz 10) (sz 4) (sz 320) (sz 3) (sz 192) (sz 2) (sz 128) (sz 800) secret_key ciphertext

let encapsulate_512_
      (public_key: Libcrux.Kem.Kyber.Types.t_KyberPublicKey (sz 800))
      (randomness: t_Array u8 (sz 32))
     =
  Libcrux.Kem.Kyber.encapsulate (sz 2) (sz 768) (sz 800) (sz 768) (sz 640) (sz 128) (sz 10) (sz 4)
    (sz 320) (sz 3) (sz 192) (sz 2) (sz 128) public_key randomness

let generate_key_pair_512_ (randomness: t_Array u8 (sz 64)) =
  Libcrux.Kem.Kyber.generate_keypair (sz 2)
    (sz 768)
    (sz 1632)
    (sz 800)
    (sz 768)
    (sz 3)
    (sz 192)
    randomness
