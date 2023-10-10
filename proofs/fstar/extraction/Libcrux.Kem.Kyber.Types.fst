module Libcrux.Kem.Kyber.Types
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let new_under_impl
      (#private_key_size #public_key_size: usize)
      (sk: array u8 v_PRIVATE_KEY_SIZE)
      (pk: array u8 v_PUBLIC_KEY_SIZE)
    : Libcrux.Kem.Kyber.t_KyberKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE =
  {
    Libcrux.Kem.Kyber.KyberKeyPair.f_sk = Core.Convert.Into.into sk;
    Libcrux.Kem.Kyber.KyberKeyPair.f_pk = Core.Convert.Into.into pk
  }

let from_under_impl
      (#private_key_size #public_key_size: usize)
      (sk: Libcrux.Kem.Kyber.t_KyberPrivateKey v_PRIVATE_KEY_SIZE)
      (pk: Libcrux.Kem.Kyber.t_KyberPublicKey v_PUBLIC_KEY_SIZE)
    : Libcrux.Kem.Kyber.t_KyberKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE =
  { Libcrux.Kem.Kyber.KyberKeyPair.f_sk = sk; Libcrux.Kem.Kyber.KyberKeyPair.f_pk = pk }

let public_key_under_impl
      (#private_key_size #public_key_size: usize)
      (self: Libcrux.Kem.Kyber.t_KyberKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
    : Libcrux.Kem.Kyber.t_KyberPublicKey v_PUBLIC_KEY_SIZE =
  self.Libcrux.Kem.Kyber.KyberKeyPair.f_pk

let private_key_under_impl
      (#private_key_size #public_key_size: usize)
      (self: Libcrux.Kem.Kyber.t_KyberKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
    : Libcrux.Kem.Kyber.t_KyberPrivateKey v_PRIVATE_KEY_SIZE =
  self.Libcrux.Kem.Kyber.KyberKeyPair.f_sk

let pk_under_impl
      (#private_key_size #public_key_size: usize)
      (self: Libcrux.Kem.Kyber.t_KyberKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
    : array u8 v_PUBLIC_KEY_SIZE =
  Libcrux.Kem.Kyber.as_slice_under_impl_35 self.Libcrux.Kem.Kyber.KyberKeyPair.f_pk

let sk_under_impl
      (#private_key_size #public_key_size: usize)
      (self: Libcrux.Kem.Kyber.t_KyberKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
    : array u8 v_PRIVATE_KEY_SIZE =
  Libcrux.Kem.Kyber.as_slice_under_impl_26 self.Libcrux.Kem.Kyber.KyberKeyPair.f_sk