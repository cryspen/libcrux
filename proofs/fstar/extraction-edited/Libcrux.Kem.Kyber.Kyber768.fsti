module Libcrux.Kem.Kyber.Kyber768
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

unfold
let t_Kyber768Ciphertext = Libcrux.Kem.Kyber.Types.t_KyberCiphertext (sz 1088)

unfold
let t_Kyber768PrivateKey = Libcrux.Kem.Kyber.Types.t_KyberPrivateKey (sz 2400)

unfold
let t_Kyber768PublicKey = Libcrux.Kem.Kyber.Types.t_KyberPublicKey (sz 1184)

val decapsulate_768_
      (secret_key: Libcrux.Kem.Kyber.Types.t_KyberPrivateKey (sz 2400))
      (ciphertext: Libcrux.Kem.Kyber.Types.t_KyberCiphertext (sz 1088))
      : Pure (t_Array u8 (sz 32))
      (requires True)
      (ensures (fun res -> res == Spec.Kyber.kyber768_decapsulate secret_key.f_value ciphertext.f_value))

val encapsulate_768_
      (public_key: Libcrux.Kem.Kyber.Types.t_KyberPublicKey (sz 1184))
      (randomness: t_Array u8 (sz 32))
    : Pure (Libcrux.Kem.Kyber.Types.t_KyberCiphertext (sz 1088) & t_Array u8 (sz 32))
      (requires True)
      (ensures (fun (ct,ss)-> (ct.f_value,ss) == Spec.Kyber.kyber768_encapsulate public_key.f_value randomness))

val generate_key_pair_768_ (randomness: t_Array u8 (sz 64))
    : Pure (Libcrux.Kem.Kyber.Types.t_KyberKeyPair (sz 2400) (sz 1184))
      (requires (True))
      (ensures (fun kp -> (kp.f_sk.f_value,kp.f_pk.f_value) == Spec.Kyber.kyber768_generate_keypair randomness))

