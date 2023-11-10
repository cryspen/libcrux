module Libcrux.Kem.Kyber.Kyber512
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let v_ETA1: usize = sz 3

let v_ETA1_RANDOMNESS_SIZE: usize = v_ETA1 *! sz 64

let v_ETA2: usize = sz 2

let v_ETA2_RANDOMNESS_SIZE: usize = v_ETA2 *! sz 64

let v_RANK_512_: usize = sz 2

let v_CPA_PKE_SECRET_KEY_SIZE_512_: usize =
  ((v_RANK_512_ *! Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT <: usize) *!
    Libcrux.Kem.Kyber.Constants.v_BITS_PER_COEFFICIENT
    <:
    usize) /!
  sz 8

let v_RANKED_BYTES_PER_RING_ELEMENT_512_: usize =
  (v_RANK_512_ *! Libcrux.Kem.Kyber.Constants.v_BITS_PER_RING_ELEMENT <: usize) /! sz 8

let v_T_AS_NTT_ENCODED_SIZE_512_: usize =
  ((v_RANK_512_ *! Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT <: usize) *!
    Libcrux.Kem.Kyber.Constants.v_BITS_PER_COEFFICIENT
    <:
    usize) /!
  sz 8

let v_CPA_PKE_PUBLIC_KEY_SIZE_512_: usize = v_T_AS_NTT_ENCODED_SIZE_512_ +! sz 32

let v_SECRET_KEY_SIZE_512_: usize =
  ((v_CPA_PKE_SECRET_KEY_SIZE_512_ +! v_CPA_PKE_PUBLIC_KEY_SIZE_512_ <: usize) +!
    Libcrux.Kem.Kyber.Constants.v_H_DIGEST_SIZE
    <:
    usize) +!
  Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE

let v_VECTOR_U_COMPRESSION_FACTOR_512_: usize = sz 10

let v_C1_BLOCK_SIZE_512_: usize =
  (Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *! v_VECTOR_U_COMPRESSION_FACTOR_512_
    <:
    usize) /!
  sz 8

let v_C1_SIZE_512_: usize = v_C1_BLOCK_SIZE_512_ *! v_RANK_512_

let v_VECTOR_V_COMPRESSION_FACTOR_512_: usize = sz 4

let v_C2_SIZE_512_: usize =
  (Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *! v_VECTOR_V_COMPRESSION_FACTOR_512_
    <:
    usize) /!
  sz 8

let v_CPA_PKE_CIPHERTEXT_SIZE_512_: usize = v_C1_SIZE_512_ +! v_C2_SIZE_512_

let v_IMPLICIT_REJECTION_HASH_INPUT_SIZE: usize =
  Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE +! v_CPA_PKE_CIPHERTEXT_SIZE_512_

unfold
let t_Kyber512Ciphertext = Libcrux.Kem.Kyber.Types.t_KyberCiphertext (sz 768)

unfold
let t_Kyber512PrivateKey = Libcrux.Kem.Kyber.Types.t_KyberPrivateKey (sz 1632)

unfold
let t_Kyber512PublicKey = Libcrux.Kem.Kyber.Types.t_KyberPublicKey (sz 800)

let decapsulate_512_
      (secret_key: Libcrux.Kem.Kyber.Types.t_KyberPrivateKey (sz 1632))
      (ciphertext: Libcrux.Kem.Kyber.Types.t_KyberCiphertext (sz 768))
    : t_Array u8 (sz 32) =
  Libcrux.Kem.Kyber.decapsulate (sz 2) (sz 1632) (sz 768) (sz 800) (sz 768) (sz 768) (sz 640)
    (sz 128) (sz 10) (sz 4) (sz 320) (sz 3) (sz 192) (sz 2) (sz 128) (sz 800) secret_key ciphertext

let encapsulate_512_
      (public_key: Libcrux.Kem.Kyber.Types.t_KyberPublicKey (sz 800))
      (randomness: t_Array u8 (sz 32))
    : Core.Result.t_Result (Libcrux.Kem.Kyber.Types.t_KyberCiphertext (sz 768) & t_Array u8 (sz 32))
      Libcrux.Kem.Kyber.Types.t_Error =
  Libcrux.Kem.Kyber.encapsulate (sz 2) (sz 768) (sz 800) (sz 768) (sz 640) (sz 128) (sz 10) (sz 4)
    (sz 320) (sz 3) (sz 192) (sz 2) (sz 128) public_key randomness

let generate_key_pair_512_ (randomness: t_Array u8 (sz 64))
    : Core.Result.t_Result (Libcrux.Kem.Kyber.Types.t_KyberKeyPair (sz 1632) (sz 800))
      Libcrux.Kem.Kyber.Types.t_Error =
  Libcrux.Kem.Kyber.generate_keypair (sz 2)
    (sz 768)
    (sz 1632)
    (sz 800)
    (sz 768)
    (sz 3)
    (sz 192)
    randomness