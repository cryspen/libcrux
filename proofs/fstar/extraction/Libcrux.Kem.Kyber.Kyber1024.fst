module Libcrux.Kem.Kyber.Kyber1024
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let v_RANK_1024_: usize = 4sz

let v_RANKED_BYTES_PER_RING_ELEMENT_1024_: usize =
  (v_RANK_1024_ *. Libcrux.Kem.Kyber.Constants.v_BITS_PER_RING_ELEMENT <: usize) /. 8sz

let v_T_AS_NTT_ENCODED_SIZE_1024_: usize =
  ((v_RANK_1024_ *. Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT <: usize) *.
    Libcrux.Kem.Kyber.Constants.v_BITS_PER_COEFFICIENT
    <:
    usize) /.
  8sz

let v_VECTOR_U_COMPRESSION_FACTOR_1024_: usize = 11sz

let v_C1_BLOCK_SIZE_1024_: usize =
  (Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *. v_VECTOR_U_COMPRESSION_FACTOR_1024_
    <:
    usize) /.
  8sz

let v_C1_SIZE_1024_: usize = v_C1_BLOCK_SIZE_1024_ *. v_RANK_1024_

let v_VECTOR_V_COMPRESSION_FACTOR_1024_: usize = 5sz

let v_C2_SIZE_1024_: usize =
  (Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *. v_VECTOR_V_COMPRESSION_FACTOR_1024_
    <:
    usize) /.
  8sz

let v_CPA_PKE_SECRET_KEY_SIZE_1024_: usize =
  ((v_RANK_1024_ *. Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT <: usize) *.
    Libcrux.Kem.Kyber.Constants.v_BITS_PER_COEFFICIENT
    <:
    usize) /.
  8sz

let v_CPA_PKE_PUBLIC_KEY_SIZE_1024_: usize = v_T_AS_NTT_ENCODED_SIZE_1024_ +. 32sz

let v_CPA_PKE_CIPHERTEXT_SIZE_1024_: usize = v_C1_SIZE_1024_ +. v_C2_SIZE_1024_

let v_SECRET_KEY_SIZE_1024_: usize =
  ((v_CPA_PKE_SECRET_KEY_SIZE_1024_ +. v_CPA_PKE_PUBLIC_KEY_SIZE_1024_ <: usize) +.
    Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE
    <:
    usize) +.
  Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE

let t_Kyber1024Ciphertext = Libcrux.Kem.Kyber.t_KyberCiphertext 1568sz

let t_Kyber1024PrivateKey = Libcrux.Kem.Kyber.t_KyberPrivateKey 3168sz

let t_Kyber1024PublicKey = Libcrux.Kem.Kyber.t_KyberPublicKey 1568sz

let t_Kyber1024SharedSecret = Libcrux.Kem.Kyber.t_KyberSharedSecret 32sz

let generate_key_pair_1024_ (randomness: array u8 64sz)
    : Core.Result.t_Result (Libcrux.Kem.Kyber.t_KyberKeyPair 3168sz 1568sz)
      Libcrux.Kem.Kyber.t_BadRejectionSamplingRandomnessError =
  Libcrux.Kem.Kyber.generate_keypair randomness

let encapsulate_1024_
      (public_key: Libcrux.Kem.Kyber.t_KyberPublicKey 1568sz)
      (randomness: array u8 32sz)
    : Core.Result.t_Result
      (Libcrux.Kem.Kyber.t_KyberCiphertext 1568sz & Libcrux.Kem.Kyber.t_KyberSharedSecret 32sz)
      Libcrux.Kem.Kyber.t_BadRejectionSamplingRandomnessError =
  Libcrux.Kem.Kyber.encapsulate public_key randomness

let decapsulate_1024_
      (secret_key: Libcrux.Kem.Kyber.t_KyberPrivateKey 3168sz)
      (ciphertext: Libcrux.Kem.Kyber.t_KyberCiphertext 1568sz)
    : array u8 32sz = Libcrux.Kem.Kyber.decapsulate secret_key ciphertext