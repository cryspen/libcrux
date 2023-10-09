module Libcrux.Kem.Kyber.Kyber1024
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let v_RANK_1024_: usize = sz 4

let v_RANKED_BYTES_PER_RING_ELEMENT_1024_: usize =
  (v_RANK_1024_ *! Libcrux.Kem.Kyber.Constants.v_BITS_PER_RING_ELEMENT <: usize) /! sz 8

let v_T_AS_NTT_ENCODED_SIZE_1024_: usize =
  ((v_RANK_1024_ *! Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT <: usize) *!
    Libcrux.Kem.Kyber.Constants.v_BITS_PER_COEFFICIENT
    <:
    usize) /!
  sz 8

let v_VECTOR_U_COMPRESSION_FACTOR_1024_: u32 = 11ul

let v_C1_BLOCK_SIZE_1024_: usize =
  (Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *!
    (cast v_VECTOR_U_COMPRESSION_FACTOR_1024_ <: usize)
    <:
    usize) /!
  sz 8

let v_C1_SIZE_1024_: usize = v_C1_BLOCK_SIZE_1024_ *! v_RANK_1024_

let v_VECTOR_V_COMPRESSION_FACTOR_1024_: u32 = 5ul

let v_C2_SIZE_1024_: usize =
  (Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *!
    (cast v_VECTOR_V_COMPRESSION_FACTOR_1024_ <: usize)
    <:
    usize) /!
  sz 8

let v_CPA_PKE_SECRET_KEY_SIZE_1024_: usize =
  ((v_RANK_1024_ *! Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT <: usize) *!
    Libcrux.Kem.Kyber.Constants.v_BITS_PER_COEFFICIENT
    <:
    usize) /!
  sz 8

let v_CPA_PKE_PUBLIC_KEY_SIZE_1024_: usize = v_T_AS_NTT_ENCODED_SIZE_1024_ +! sz 32

let v_CPA_PKE_CIPHERTEXT_SIZE_1024_: usize = v_C1_SIZE_1024_ +! v_C2_SIZE_1024_

let v_SECRET_KEY_SIZE_1024_: usize =
  ((v_CPA_PKE_SECRET_KEY_SIZE_1024_ +! v_CPA_PKE_PUBLIC_KEY_SIZE_1024_ <: usize) +!
    Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE
    <:
    usize) +!
  Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE

let t_Kyber1024Ciphertext = Libcrux.Kem.Kyber.t_KyberCiphertext (sz 1568)

let t_Kyber1024PrivateKey = Libcrux.Kem.Kyber.t_KyberPrivateKey (sz 3168)

let t_Kyber1024PublicKey = Libcrux.Kem.Kyber.t_KyberPublicKey (sz 1568)

let t_Kyber1024SharedSecret = Libcrux.Kem.Kyber.t_KyberSharedSecret (sz 32)

let generate_key_pair_1024_ (randomness: array u8 (sz 64))
    : Core.Result.t_Result (Libcrux.Kem.Kyber.t_KyberKeyPair (sz 3168) (sz 1568))
      Libcrux.Kem.Kyber.t_BadRejectionSamplingRandomnessError =
  Libcrux.Kem.Kyber.generate_keypair randomness

let encapsulate_1024_
      (public_key: Libcrux.Kem.Kyber.t_KyberPublicKey (sz 1568))
      (randomness: array u8 (sz 32))
    : Core.Result.t_Result
      (Libcrux.Kem.Kyber.t_KyberCiphertext (sz 1568) & Libcrux.Kem.Kyber.t_KyberSharedSecret (sz 32)
      ) Libcrux.Kem.Kyber.t_BadRejectionSamplingRandomnessError =
  Libcrux.Kem.Kyber.encapsulate public_key randomness

let decapsulate_1024_
      (secret_key: Libcrux.Kem.Kyber.t_KyberPrivateKey (sz 3168))
      (ciphertext: Libcrux.Kem.Kyber.t_KyberCiphertext (sz 1568))
    : array u8 (sz 32) = Libcrux.Kem.Kyber.decapsulate secret_key ciphertext