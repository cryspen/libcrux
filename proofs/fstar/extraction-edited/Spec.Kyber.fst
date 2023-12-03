module Spec.Kyber
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

(** Constants *)
let v_BITS_PER_COEFFICIENT: usize = sz 12

let v_COEFFICIENTS_IN_RING_ELEMENT: usize = sz 256

let v_BITS_PER_RING_ELEMENT: usize = v_COEFFICIENTS_IN_RING_ELEMENT *! sz 12

let v_BYTES_PER_RING_ELEMENT: usize = v_BITS_PER_RING_ELEMENT /! sz 8

let v_CPA_PKE_KEY_GENERATION_SEED_SIZE: usize = sz 32

let v_FIELD_MODULUS: i32 = 3329l

let v_H_DIGEST_SIZE: usize =
  Libcrux.Digest.digest_size (Libcrux.Digest.Algorithm_Sha3_256_ <: Libcrux.Digest.t_Algorithm)

let v_REJECTION_SAMPLING_SEED_SIZE: usize = sz 168 *! sz 5

let v_SHARED_SECRET_SIZE: usize = sz 32

type params_ = {
    v_RANK: usize;
    v_ETA1: usize;
    v_ETA2: usize;
    v_VECTOR_U_COMPRESSION_FACTOR: usize;
    v_VECTOR_V_COMPRESSION_FACTOR: usize;
}

let valid_params p =
  p.v_RANK >=. sz 2 && p.v_RANK <=. sz 4 &&
  p.v_ETA1 <=. sz 3 &&
  p.v_ETA2 <=. sz 2 &&
  (p.v_VECTOR_U_COMPRESSION_FACTOR = sz 10 || p.v_VECTOR_U_COMPRESSION_FACTOR = sz 11) &&
  (p.v_VECTOR_V_COMPRESSION_FACTOR = sz 4 || p.v_VECTOR_V_COMPRESSION_FACTOR = sz 5)

let params = p:params_{valid_params p}

let v_ETA1_RANDOMNESS_SIZE (p:params) = p.v_ETA1 *! sz 64
let v_ETA2_RANDOMNESS_SIZE (p:params) = p.v_ETA2 *! sz 64

let v_RANKED_BYTES_PER_RING_ELEMENT (p:params)  =
  (p.v_RANK *! v_BITS_PER_RING_ELEMENT) /! sz 8

let v_T_AS_NTT_ENCODED_SIZE (p:params) =
  ((p.v_RANK *! v_COEFFICIENTS_IN_RING_ELEMENT *! v_BITS_PER_COEFFICIENT) /! sz 8)

let v_CPA_PKE_SECRET_KEY_SIZE (p:params) =
  ((p.v_RANK *! v_COEFFICIENTS_IN_RING_ELEMENT *! v_BITS_PER_COEFFICIENT) /! sz 8)

let v_CPA_PKE_PUBLIC_KEY_SIZE (p:params) = v_T_AS_NTT_ENCODED_SIZE p +! sz 32

let v_SECRET_KEY_SIZE (p:params) =
  (v_CPA_PKE_SECRET_KEY_SIZE p +! v_CPA_PKE_PUBLIC_KEY_SIZE p +! v_H_DIGEST_SIZE +! v_SHARED_SECRET_SIZE)

let v_C1_BLOCK_SIZE (p:params) =
  (v_COEFFICIENTS_IN_RING_ELEMENT *! p.v_VECTOR_U_COMPRESSION_FACTOR) /! sz 8

let v_C1_SIZE (p:params) = v_C1_BLOCK_SIZE p *! p.v_RANK

let v_C2_SIZE (p:params) =
  (v_COEFFICIENTS_IN_RING_ELEMENT *! p.v_VECTOR_V_COMPRESSION_FACTOR) /! sz 8

let v_CPA_PKE_CIPHERTEXT_SIZE (p:params) = v_C1_SIZE p +! v_C2_SIZE p

let v_IMPLICIT_REJECTION_HASH_INPUT_SIZE (p:params) =
    v_SHARED_SECRET_SIZE +! v_CPA_PKE_CIPHERTEXT_SIZE p

let v_KEY_GENERATION_SEED_SIZE: usize =
  v_CPA_PKE_KEY_GENERATION_SEED_SIZE +!
  v_SHARED_SECRET_SIZE

(** Types *)

type t_Error = | Error_RejectionSampling : t_Error

type t_Result a b = 
  | Ok: a -> t_Result a b
  | Err: b -> t_Result a b

type t_KyberPublicKey (p:params) = t_Array u8 (v_CPA_PKE_PUBLIC_KEY_SIZE p)
type t_KyberPrivateKey (p:params) = t_Array u8 (v_SECRET_KEY_SIZE p)
type t_KyberKeyPair (p:params) = t_KyberPrivateKey p & t_KyberPublicKey p

type t_KyberCiphertext (p:params) = t_Array u8 (v_CPA_PKE_CIPHERTEXT_SIZE p)
type t_KyberSharedSecret = t_Array u8 (v_SHARED_SECRET_SIZE)

(** IND-CCA Functions *)

assume val ind_cca_generate_keypair (p:params) (randomness:t_Array u8 v_KEY_GENERATION_SEED_SIZE) :
                                    t_Result (t_KyberKeyPair p) t_Error

assume val ind_cca_encapsulate (p:params) (public_key: t_KyberPublicKey p)
                               (randomness:t_Array u8 v_SHARED_SECRET_SIZE) :
                                t_Result (t_KyberCiphertext p &  t_KyberSharedSecret) t_Error

assume val ind_cca_decapsulate (p:params) (secret_key: t_KyberPrivateKey p)
                               (ciphertext: t_KyberCiphertext p): 
                               t_KyberSharedSecret

(** Kyber-768 Instantiation *)

let kyber768_params : params = {
    v_RANK = sz 3;
    v_ETA1 = sz 2;
    v_ETA2 = sz 2;
    v_VECTOR_U_COMPRESSION_FACTOR = sz 10;
    v_VECTOR_V_COMPRESSION_FACTOR = sz 4;
}

let kyber768_generate_keypair (randomness:t_Array u8 (sz 64)):
                              t_Result (t_Array u8 (sz 2400) & t_Array u8 (sz 1184)) t_Error =
    ind_cca_generate_keypair kyber768_params randomness

let kyber768_encapsulate (public_key: t_Array u8 (sz 1184)) (randomness: t_Array u8 (sz 32)):
                         t_Result (t_Array u8 (sz 1088) & t_Array u8 (sz 32)) t_Error =
    ind_cca_encapsulate kyber768_params public_key randomness


let kyber768_decapsulate (secret_key: t_Array u8 (sz 2400)) (ciphertext: t_Array u8 (sz 1088)):
                         t_Array u8 (sz 32) =
    ind_cca_decapsulate kyber768_params secret_key ciphertext

(** Kyber-1024 Instantiation *)

let kyber1024_params : params = {
    v_RANK = sz 4;
    v_ETA1 = sz 2;
    v_ETA2 = sz 2;
    v_VECTOR_U_COMPRESSION_FACTOR = sz 11;
    v_VECTOR_V_COMPRESSION_FACTOR = sz 5;
}

let kyber1024_generate_keypair (randomness:t_Array u8 (sz 64)):
                               t_Result (t_Array u8 (sz 3168) & t_Array u8 (sz 1568)) t_Error =
    ind_cca_generate_keypair kyber1024_params randomness

let kyber1024_encapsulate (public_key: t_Array u8 (sz 1568)) (randomness: t_Array u8 (sz 32)):
                         t_Result (t_Array u8 (sz 1568) & t_Array u8 (sz 32)) t_Error =
    ind_cca_encapsulate kyber1024_params public_key randomness


let kyber1024_decapsulate (secret_key: t_Array u8 (sz 3168)) (ciphertext: t_Array u8 (sz 1568)):
                         t_Array u8 (sz 32) =
    ind_cca_decapsulate kyber1024_params secret_key ciphertext

(** Kyber-512 Instantiation *)

let kyber512_params : params = {
    v_RANK = sz 2;
    v_ETA1 = sz 3;
    v_ETA2 = sz 2;
    v_VECTOR_U_COMPRESSION_FACTOR = sz 10;
    v_VECTOR_V_COMPRESSION_FACTOR = sz 4;
}

let kyber512_generate_keypair (randomness:t_Array u8 (sz 64)):
                              t_Result (t_Array u8 (sz 1632) & t_Array u8 (sz 800)) t_Error  =
    ind_cca_generate_keypair kyber512_params randomness

let kyber512_encapsulate (public_key: t_Array u8 (sz 800)) (randomness: t_Array u8 (sz 32)):
                         t_Result (t_Array u8 (sz 768) & t_Array u8 (sz 32)) t_Error =
    ind_cca_encapsulate kyber512_params public_key randomness


let kyber512_decapsulate (secret_key: t_Array u8 (sz 1632)) (ciphertext: t_Array u8 (sz 768)):
                         t_Array u8 (sz 32) =
    ind_cca_decapsulate kyber512_params secret_key ciphertext
