module Libcrux.Kem.Kyber.Kyber512
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let v_RANK_512_: usize = 2sz

let v_RANKED_BYTES_PER_RING_ELEMENT_512_: usize =
  (v_RANK_512_ *. Libcrux.Kem.Kyber.Constants.v_BITS_PER_RING_ELEMENT <: usize) /. 8sz

let v_T_AS_NTT_ENCODED_SIZE_512_: usize =
  ((v_RANK_512_ *. Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT <: usize) *.
    Libcrux.Kem.Kyber.Constants.v_BITS_PER_COEFFICIENT
    <:
    usize) /.
  8sz

let v_VECTOR_U_COMPRESSION_FACTOR_512_: usize = 10sz

let v_C1_BLOCK_SIZE_512_: usize =
  (Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *. v_VECTOR_U_COMPRESSION_FACTOR_512_
    <:
    usize) /.
  8sz

let v_C1_SIZE_512_: usize = v_C1_BLOCK_SIZE_512_ *. v_RANK_512_

let v_VECTOR_V_COMPRESSION_FACTOR_512_: usize = 4sz

let v_C2_SIZE_512_: usize =
  (Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *. v_VECTOR_V_COMPRESSION_FACTOR_512_
    <:
    usize) /.
  8sz

let v_CPA_PKE_SECRET_KEY_SIZE_512_: usize =
  ((v_RANK_512_ *. Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT <: usize) *.
    Libcrux.Kem.Kyber.Constants.v_BITS_PER_COEFFICIENT
    <:
    usize) /.
  8sz

let v_CPA_PKE_PUBLIC_KEY_SIZE_512_: usize = v_T_AS_NTT_ENCODED_SIZE_512_ +. 32sz

let v_CPA_PKE_CIPHERTEXT_SIZE_512_: usize = v_C1_SIZE_512_ +. v_C2_SIZE_512_

let v_SECRET_KEY_SIZE_512_: usize =
  ((v_CPA_PKE_SECRET_KEY_SIZE_512_ +. v_CPA_PKE_PUBLIC_KEY_SIZE_512_ <: usize) +.
    Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE
    <:
    usize) +.
  Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE

let v_ETA1: usize = 3sz

let v_ETA1_RANDOMNESS_SIZE: usize = v_ETA1 *. 64sz

let v_ETA2: usize = 2sz

let v_ETA2_RANDOMNESS_SIZE: usize = v_ETA2 *. 64sz

let t_Kyber512Ciphertext = Libcrux.Kem.Kyber.t_KyberCiphertext 768sz

let t_Kyber512PrivateKey = Libcrux.Kem.Kyber.t_KyberPrivateKey 1632sz

let t_Kyber512PublicKey = Libcrux.Kem.Kyber.t_KyberPublicKey 800sz

let t_Kyber512SharedSecret = Libcrux.Kem.Kyber.t_KyberSharedSecret 32sz

let generate_key_pair_512_ (randomness: array u8 64sz)
    : Core.Result.t_Result (Libcrux.Kem.Kyber.t_KyberKeyPair 1632sz 800sz)
      Libcrux.Kem.Kyber.t_BadRejectionSamplingRandomnessError =
  Libcrux.Kem.Kyber.generate_keypair randomness

let encapsulate_512_
      (public_key: Libcrux.Kem.Kyber.t_KyberPublicKey 800sz)
      (randomness: array u8 32sz)
    : Core.Result.t_Result
      (Libcrux.Kem.Kyber.t_KyberCiphertext 768sz & Libcrux.Kem.Kyber.t_KyberSharedSecret 32sz)
      Libcrux.Kem.Kyber.t_BadRejectionSamplingRandomnessError =
  Libcrux.Kem.Kyber.encapsulate public_key randomness

let decapsulate_512_
      (secret_key: Libcrux.Kem.Kyber.t_KyberPrivateKey 1632sz)
      (ciphertext: Libcrux.Kem.Kyber.t_KyberCiphertext 768sz)
    : array u8 32sz = Libcrux.Kem.Kyber.decapsulate secret_key ciphertext