module Libcrux_ml_kem.Types
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let impl_7__len (v_SIZE: usize) (_: Prims.unit) = v_SIZE

let impl_14__len (v_SIZE: usize) (_: Prims.unit) = v_SIZE

let impl_21__len (v_SIZE: usize) (_: Prims.unit) = v_SIZE

let unpack_private_key (v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE: usize) (private_key: t_Slice u8) =
  let ind_cpa_secret_key, secret_key:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8 private_key v_CPA_SECRET_KEY_SIZE
  in
  let ind_cpa_public_key, secret_key:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8 secret_key v_PUBLIC_KEY_SIZE
  in
  let ind_cpa_public_key_hash, implicit_rejection_value:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8 secret_key Libcrux_ml_kem.Constants.v_H_DIGEST_SIZE
  in
  ind_cpa_secret_key, ind_cpa_public_key, ind_cpa_public_key_hash, implicit_rejection_value
  <:
  (t_Slice u8 & t_Slice u8 & t_Slice u8 & t_Slice u8)

let impl_7__as_slice (v_SIZE: usize) (self: t_MlKemCiphertext v_SIZE) = self.f_value

let impl_14__as_slice (v_SIZE: usize) (self: t_MlKemPrivateKey v_SIZE) = self.f_value

let impl_21__as_slice (v_SIZE: usize) (self: t_MlKemPublicKey v_SIZE) = self.f_value

let impl__from
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (sk: t_MlKemPrivateKey v_PRIVATE_KEY_SIZE)
      (pk: t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
     = { f_sk = sk; f_pk = pk } <: t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE

let impl__into_parts
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (self: t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
     =
  self.f_sk, self.f_pk
  <:
  (t_MlKemPrivateKey v_PRIVATE_KEY_SIZE & t_MlKemPublicKey v_PUBLIC_KEY_SIZE)

let impl__new
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (sk: t_Array u8 v_PRIVATE_KEY_SIZE)
      (pk: t_Array u8 v_PUBLIC_KEY_SIZE)
     =
  {
    f_sk
    =
    Core.Convert.f_into #(t_Array u8 v_PRIVATE_KEY_SIZE)
      #(t_MlKemPrivateKey v_PRIVATE_KEY_SIZE)
      #FStar.Tactics.Typeclasses.solve
      sk;
    f_pk
    =
    Core.Convert.f_into #(t_Array u8 v_PUBLIC_KEY_SIZE)
      #(t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
      #FStar.Tactics.Typeclasses.solve
      pk
  }
  <:
  t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE

let impl__pk
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (self: t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
     = impl_21__as_slice v_PUBLIC_KEY_SIZE self.f_pk

let impl__private_key
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (self: t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
     = self.f_sk

let impl__public_key
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (self: t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
     = self.f_pk

let impl__sk
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (self: t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
     = impl_14__as_slice v_PRIVATE_KEY_SIZE self.f_sk
