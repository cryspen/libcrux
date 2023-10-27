module Libcrux.Kem.Kyber.Kyber768
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let v_RANK_768_: usize = sz 3

let v_RANKED_BYTES_PER_RING_ELEMENT_768_: usize =
  (v_RANK_768_ *! Libcrux.Kem.Kyber.Constants.v_BITS_PER_RING_ELEMENT <: usize) /! sz 8

let v_T_AS_NTT_ENCODED_SIZE_768_: usize =
  ((v_RANK_768_ *! Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT <: usize) *!
    Libcrux.Kem.Kyber.Constants.v_BITS_PER_COEFFICIENT
    <:
    usize) /!
  sz 8

let v_VECTOR_U_COMPRESSION_FACTOR_768_: usize = sz 10

let v_C1_BLOCK_SIZE_768_: usize =
  (Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *! v_VECTOR_U_COMPRESSION_FACTOR_768_
    <:
    usize) /!
  sz 8

let v_C1_SIZE_768_: usize = v_C1_BLOCK_SIZE_768_ *! v_RANK_768_

let v_VECTOR_V_COMPRESSION_FACTOR_768_: usize = sz 4

let v_C2_SIZE_768_: usize =
  (Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *! v_VECTOR_V_COMPRESSION_FACTOR_768_
    <:
    usize) /!
  sz 8

let v_CPA_PKE_SECRET_KEY_SIZE_768_: usize =
  ((v_RANK_768_ *! Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT <: usize) *!
    Libcrux.Kem.Kyber.Constants.v_BITS_PER_COEFFICIENT
    <:
    usize) /!
  sz 8

let v_CPA_PKE_PUBLIC_KEY_SIZE_768_: usize = v_T_AS_NTT_ENCODED_SIZE_768_ +! sz 32

let v_CPA_PKE_CIPHERTEXT_SIZE_768_: usize = v_C1_SIZE_768_ +! v_C2_SIZE_768_

let v_SECRET_KEY_SIZE_768_: usize =
  ((v_CPA_PKE_SECRET_KEY_SIZE_768_ +! v_CPA_PKE_PUBLIC_KEY_SIZE_768_ <: usize) +!
    Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE
    <:
    usize) +!
  Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE

let v_ETA1: usize = sz 2

let v_ETA1_RANDOMNESS_SIZE: usize = v_ETA1 *! sz 64

let v_ETA2: usize = sz 2

let v_ETA2_RANDOMNESS_SIZE: usize = v_ETA2 *! sz 64

let v_IMPLICIT_REJECTION_HASH_INPUT_SIZE: usize =
  Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE +! v_CPA_PKE_CIPHERTEXT_SIZE_768_

let t_Kyber768Ciphertext = Libcrux.Kem.Kyber.Types.t_KyberCiphertext (sz 1088)

let t_Kyber768PrivateKey = Libcrux.Kem.Kyber.Types.t_KyberPrivateKey (sz 2400)

let t_Kyber768PublicKey = Libcrux.Kem.Kyber.Types.t_KyberPublicKey (sz 1184)

let generate_key_pair_768_ (randomness: t_Array u8 (sz 64))
    : Core.Result.t_Result (Libcrux.Kem.Kyber.Types.t_KyberKeyPair (sz 2400) (sz 1184))
      Libcrux.Kem.Kyber.Types.t_Error = Libcrux.Kem.Kyber.generate_keypair randomness

let encapsulate_768_
      (public_key: Libcrux.Kem.Kyber.Types.t_KyberPublicKey (sz 1184))
      (randomness: t_Array u8 (sz 32))
    : Core.Result.t_Result
      (Libcrux.Kem.Kyber.Types.t_KyberCiphertext (sz 1088) & t_Array u8 (sz 32))
      Libcrux.Kem.Kyber.Types.t_Error = Libcrux.Kem.Kyber.encapsulate public_key randomness

let decapsulate_768_
      (secret_key: Libcrux.Kem.Kyber.Types.t_KyberPrivateKey (sz 2400))
      (ciphertext: Libcrux.Kem.Kyber.Types.t_KyberCiphertext (sz 1088))
    : t_Array u8 (sz 32) = Libcrux.Kem.Kyber.decapsulate secret_key ciphertext