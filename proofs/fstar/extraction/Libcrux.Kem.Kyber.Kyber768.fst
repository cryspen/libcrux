module Libcrux.Kem.Kyber.Kyber768
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let v_RANK_768_: usize = 3sz

let v_RANKED_BYTES_PER_RING_ELEMENT_768_: usize =
  (v_RANK_768_ *. Libcrux.Kem.Kyber.Constants.v_BITS_PER_RING_ELEMENT <: usize) /. 8sz

let v_T_AS_NTT_ENCODED_SIZE_768_: usize =
  ((v_RANK_768_ *. Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT <: usize) *.
    Libcrux.Kem.Kyber.Constants.v_BITS_PER_COEFFICIENT
    <:
    usize) /.
  8sz

let v_VECTOR_U_COMPRESSION_FACTOR_768_: usize = 10sz

let v_C1_BLOCK_SIZE_768_: usize =
  (Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *. v_VECTOR_U_COMPRESSION_FACTOR_768_
    <:
    usize) /.
  8sz

let v_C1_SIZE_768_: usize = v_C1_BLOCK_SIZE_768_ *. v_RANK_768_

let v_VECTOR_V_COMPRESSION_FACTOR_768_: usize = 4sz

let v_C2_SIZE_768_: usize =
  (Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *. v_VECTOR_V_COMPRESSION_FACTOR_768_
    <:
    usize) /.
  8sz

let v_CPA_PKE_SECRET_KEY_SIZE_768_: usize =
  ((v_RANK_768_ *. Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT <: usize) *.
    Libcrux.Kem.Kyber.Constants.v_BITS_PER_COEFFICIENT
    <:
    usize) /.
  8sz

let v_CPA_PKE_PUBLIC_KEY_SIZE_768_: usize = v_T_AS_NTT_ENCODED_SIZE_768_ +. 32sz

let v_CPA_PKE_CIPHERTEXT_SIZE_768_: usize = v_C1_SIZE_768_ +. v_C2_SIZE_768_

let v_SECRET_KEY_SIZE_768_: usize =
  ((v_CPA_PKE_SECRET_KEY_SIZE_768_ +. v_CPA_PKE_PUBLIC_KEY_SIZE_768_ <: usize) +.
    Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE
    <:
    usize) +.
  Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE

let v_ETA1: usize = 2sz

let v_ETA1_RANDOMNESS_SIZE: usize = v_ETA1 *. 64sz

let v_ETA2: usize = 2sz

let v_ETA2_RANDOMNESS_SIZE: usize = v_ETA2 *. 64sz

let t_Kyber768Ciphertext = Libcrux.Kem.Kyber.t_KyberCiphertext 1088sz

let t_Kyber768PrivateKey = Libcrux.Kem.Kyber.t_KyberPrivateKey 2400sz

let t_Kyber768PublicKey = Libcrux.Kem.Kyber.t_KyberPublicKey 1184sz

let t_Kyber768SharedSecret = Libcrux.Kem.Kyber.t_KyberSharedSecret 32sz

let generate_key_pair_768_ (randomness: array u8 64sz)
    : Core.Result.t_Result (Libcrux.Kem.Kyber.t_KyberKeyPair 2400sz 1184sz)
      Libcrux.Kem.Kyber.t_BadRejectionSamplingRandomnessError =
  Libcrux.Kem.Kyber.generate_keypair randomness

let encapsulate_768_
      (public_key: Libcrux.Kem.Kyber.t_KyberPublicKey 1184sz)
      (randomness: array u8 32sz)
    : Core.Result.t_Result
      (Libcrux.Kem.Kyber.t_KyberCiphertext 1088sz & Libcrux.Kem.Kyber.t_KyberSharedSecret 32sz)
      Libcrux.Kem.Kyber.t_BadRejectionSamplingRandomnessError =
  Libcrux.Kem.Kyber.encapsulate public_key randomness

let decapsulate_768_
      (secret_key: Libcrux.Kem.Kyber.t_KyberPrivateKey 2400sz)
      (ciphertext: Libcrux.Kem.Kyber.t_KyberCiphertext 1088sz)
    : array u8 32sz = Libcrux.Kem.Kyber.decapsulate secret_key ciphertext