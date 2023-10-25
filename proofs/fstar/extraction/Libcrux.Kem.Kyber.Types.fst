module Libcrux.Kem.Kyber.Types
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let impl__new
      (#v_PRIVATE_KEY_SIZE #v_PUBLIC_KEY_SIZE: usize)
      (sk: t_Array u8 v_PRIVATE_KEY_SIZE)
      (pk: t_Array u8 v_PUBLIC_KEY_SIZE)
    : Libcrux.Kem.Kyber.t_KyberKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE =
  {
    Libcrux.Kem.Kyber.f_sk = Core.Convert.f_into sk;
    Libcrux.Kem.Kyber.f_pk = Core.Convert.f_into pk
  }

let impl__from
      (#v_PRIVATE_KEY_SIZE #v_PUBLIC_KEY_SIZE: usize)
      (sk: Libcrux.Kem.Kyber.t_KyberPrivateKey v_PRIVATE_KEY_SIZE)
      (pk: Libcrux.Kem.Kyber.t_KyberPublicKey v_PUBLIC_KEY_SIZE)
    : Libcrux.Kem.Kyber.t_KyberKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE =
  { Libcrux.Kem.Kyber.f_sk = sk; Libcrux.Kem.Kyber.f_pk = pk }

let impl__public_key
      (#v_PRIVATE_KEY_SIZE #v_PUBLIC_KEY_SIZE: usize)
      (self: Libcrux.Kem.Kyber.t_KyberKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
    : Libcrux.Kem.Kyber.t_KyberPublicKey v_PUBLIC_KEY_SIZE = self.Libcrux.Kem.Kyber.f_pk

let impl__private_key
      (#v_PRIVATE_KEY_SIZE #v_PUBLIC_KEY_SIZE: usize)
      (self: Libcrux.Kem.Kyber.t_KyberKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
    : Libcrux.Kem.Kyber.t_KyberPrivateKey v_PRIVATE_KEY_SIZE = self.Libcrux.Kem.Kyber.f_sk

let impl__pk
      (#v_PRIVATE_KEY_SIZE #v_PUBLIC_KEY_SIZE: usize)
      (self: Libcrux.Kem.Kyber.t_KyberKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
    : t_Array u8 v_PUBLIC_KEY_SIZE = Libcrux.Kem.Kyber.impl_29__as_slice self.Libcrux.Kem.Kyber.f_pk

let impl__sk
      (#v_PRIVATE_KEY_SIZE #v_PUBLIC_KEY_SIZE: usize)
      (self: Libcrux.Kem.Kyber.t_KyberKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
    : t_Array u8 v_PRIVATE_KEY_SIZE =
  Libcrux.Kem.Kyber.impl_19__as_slice self.Libcrux.Kem.Kyber.f_sk