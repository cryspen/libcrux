module Spec.Kyber
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
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

// KB: This needs to be the same as v_H_DIGEST_SIZE no?
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
  (p.v_ETA1 = sz 2 || p.v_ETA1 = sz 3) &&
  p.v_ETA2 =. sz 2 &&
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

let v_IMPLICIT_REJECTION_HASH_INPUT_SIZE (p:params)
  : x:usize{v x == v v_SHARED_SECRET_SIZE + v #usize_inttype (v_CPA_PKE_CIPHERTEXT_SIZE p)} =
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

type t_KyberCPAPrivateKey (p:params) = t_Array u8 (v_CPA_PKE_SECRET_KEY_SIZE p)
type t_KyberCPAKeyPair (p:params) = t_KyberCPAPrivateKey p & t_KyberPublicKey p

type t_KyberCiphertext (p:params) = t_Array u8 (v_CPA_PKE_CIPHERTEXT_SIZE p)
type t_KyberSharedSecret = t_Array u8 (v_SHARED_SECRET_SIZE)

(** Utility and Hash Function *)
let concat #t (x:t_Slice t) (y:t_Slice t{range (v (length x) + v (length y)) usize_inttype}) :
           r:t_Array t (length x +! length y) = Seq.append x y

assume val lemma_index_concat #t (x:t_Slice t) (y:t_Slice t{range (v (length x) + v (length y)) usize_inttype}) (i:usize{i <. length x +! length y}):
           Lemma (if i <. length x then
                    Seq.index (concat x y) (v i) == x.[i]
                  else 
                    Seq.index (concat x y) (v i) == y.[i -! length x])
           [SMTPat (Seq.index (concat #t x y) i)]

let slice #t (x:t_Slice t) (i:usize{i <=. length x}) (j:usize{i <=. j /\ j <=. length x}):
           r:t_Array t (j -! i) = Seq.slice x (v i) (v j)

assume val lemma_index_slice #t (x:t_Slice t) (i:usize{i <=. length x}) (j:usize{i <=. j /\ j <=. length x})
                                (k:usize{k <. j -! i}):
           Lemma (Seq.index (slice x i j) (v k) == x.[i +! k])
           [SMTPat (Seq.index (slice x i j) (v k))]

assume val eq_intro #t (a : Seq.seq t) (b:Seq.seq t{Seq.length a == Seq.length b}):
       Lemma
       (requires forall i. {:pattern Seq.index a i; Seq.index b i}
                      i < Seq.length a ==>
                      Seq.index a i == Seq.index b i)
       (ensures Seq.equal a b)
       [SMTPat (Seq.equal a b)]

let split #t (a:t_Slice t) (m:usize{m <=. length a}):
       Pure (t_Array t m & t_Array t (length a -! m))
       True (ensures (fun (x,y) ->
         x == slice a (sz 0) m /\
         y == slice a m (length a) /\
         concat #t x y == a)) = 
         let x = Seq.slice a 0 (v m) in
         let y = Seq.slice a (v m) (Seq.length a) in
         assert (Seq.equal a (concat x y));
         (x,y)

let lemma_slice_append #t (x:t_Slice t) (y:t_Slice t) (z:t_Slice t):
  Lemma (requires (range (v (length y) + v (length z)) usize_inttype /\
                   length y +! length z == length x /\
                   y == slice x (sz 0) (length y) /\ 
                   z == slice x (length y) (length x)))
        (ensures (x == concat y z)) = 
        assert (Seq.equal x (concat y z))

let lemma_slice_append_3 #t (x:t_Slice t) (y:t_Slice t) (z:t_Slice t) (w:t_Slice t):
  Lemma (requires (range (v (length y) + v (length z) + v (length w)) usize_inttype /\
                   length y +! length z +! length w == length x /\
                   y == slice x (sz 0) (length y) /\ 
                   z == slice x (length y) (length y +! length z) /\
                   w == slice x (length y +! length z) (length x)))
        (ensures (x == concat y (concat z w))) =
         assert (Seq.equal x (Seq.append y (Seq.append z w)))

let lemma_slice_append_4 #t (x y z w u:t_Slice t) :
  Lemma (requires (range (v (length y) + v (length z) + v (length w) + v (length u)) usize_inttype /\
                   length y +! length z +! length w +! length u == length x /\
                   y == slice x (sz 0) (length y) /\ 
                   z == slice x (length y) (length y +! length z) /\
                   w == slice x (length y +! length z) (length y +! length z +! length w) /\
                   u == slice x (length y +! length z +! length w) (length x)))
        (ensures (x == concat y (concat z (concat w u)))) =
         assert (Seq.equal x (Seq.append y (Seq.append z (Seq.append w u))))


assume val v_G (input: t_Slice u8) : t_Array u8 (sz 64)
assume val v_H (input: t_Slice u8) : t_Array u8 (sz 32)
assume val v_PRF (v_LEN: usize) (input: t_Slice u8) : t_Array u8 v_LEN
let v_J (input: t_Slice u8) : t_Array u8 (sz 32) = v_PRF (sz 32) input
assume val v_XOF (v_LEN: usize) (input: t_Slice u8) : t_Array u8 v_LEN

(** IND-CPA Functions *)

assume val ind_cpa_generate_keypair (p:params) (randomness:t_Array u8 v_CPA_PKE_KEY_GENERATION_SEED_SIZE) :
                                    t_KyberCPAKeyPair p

assume val ind_cpa_encrypt (p:params) (public_key: t_KyberPublicKey p)
                           (message: t_Array u8 v_SHARED_SECRET_SIZE)
                           (randomness:t_Array u8 v_SHARED_SECRET_SIZE) :
                            t_KyberCiphertext p

assume val ind_cpa_decrypt (p:params) (secret_key: t_KyberCPAPrivateKey p)
                               (ciphertext: t_KyberCiphertext p): 
                               t_KyberSharedSecret


(** IND-CCA Functions *)


/// This function implements most of Algorithm 15 of the
/// NIST FIPS 203 specification; this is the Kyber CCA-KEM key generation algorithm.
///
/// We say "most of" since Algorithm 15 samples the required randomness within
/// the function itself, whereas this implementation expects it to be provided
/// through the `randomness` parameter.
/// 
/// TODO: input validation

val ind_cca_generate_keypair (p:params) (randomness:t_Array u8 v_KEY_GENERATION_SEED_SIZE) :
                             t_KyberKeyPair p
let ind_cca_generate_keypair p randomness =
    let (ind_cpa_keypair_randomness, implicit_rejection_value) =
        split randomness v_CPA_PKE_KEY_GENERATION_SEED_SIZE in
        
    let (ind_cpa_secret_key,ind_cpa_public_key) = ind_cpa_generate_keypair p ind_cpa_keypair_randomness in
    let ind_cca_secret_key = Seq.append ind_cpa_secret_key (
                             Seq.append ind_cpa_public_key (
                             Seq.append (v_H ind_cpa_public_key) implicit_rejection_value)) in
    (ind_cca_secret_key, ind_cpa_public_key)

/// This function implements most of Algorithm 16 of the
/// NIST FIPS 203 specification; this is the Kyber CCA-KEM encapsulation algorithm.
///
/// We say "most of" since Algorithm 16 samples the required randomness within
/// the function itself, whereas this implementation expects it to be provided
/// through the `randomness` parameter.
///
/// TODO: input validation

val ind_cca_encapsulate (p:params) (public_key: t_KyberPublicKey p)
                        (randomness:t_Array u8 v_SHARED_SECRET_SIZE) :
                        (t_KyberCiphertext p &  t_KyberSharedSecret)
let ind_cca_encapsulate p public_key randomness =
    let to_hash = concat randomness (v_H public_key) in
    let hashed = v_G to_hash in
    let (shared_secret, pseudorandomness) = split hashed v_SHARED_SECRET_SIZE in
    let ciphertext = ind_cpa_encrypt p public_key randomness pseudorandomness in
    (ciphertext,shared_secret)
    

/// This function implements Algorithm 17 of the
/// NIST FIPS 203 specification; this is the Kyber CCA-KEM encapsulation algorithm.

val ind_cca_decapsulate (p:params) (secret_key: t_KyberPrivateKey p)
                        (ciphertext: t_KyberCiphertext p): 
                         t_KyberSharedSecret
let ind_cca_decapsulate p secret_key ciphertext =
    let (ind_cpa_secret_key,rest) = split secret_key (v_CPA_PKE_SECRET_KEY_SIZE p) in
    let (ind_cpa_public_key,rest) = split rest (v_CPA_PKE_PUBLIC_KEY_SIZE p) in
    let (ind_cpa_public_key_hash,implicit_rejection_value) = split rest v_H_DIGEST_SIZE in
    
    let decrypted = ind_cpa_decrypt p ind_cpa_secret_key ciphertext in
    let to_hash = concat decrypted ind_cpa_public_key_hash in
    let hashed = v_G to_hash in
    let (success_shared_secret, pseudorandomness) = split hashed v_SHARED_SECRET_SIZE in

    assert (Seq.length implicit_rejection_value = 32);
    let to_hash = concat implicit_rejection_value ciphertext in
    let rejection_shared_secret = v_J to_hash in

    let reencrypted = ind_cpa_encrypt p ind_cpa_public_key decrypted pseudorandomness in
    if reencrypted = ciphertext
    then success_shared_secret
    else rejection_shared_secret
   

(** Kyber-768 Instantiation *)

let kyber768_params : params = {
    v_RANK = sz 3;
    v_ETA1 = sz 2;
    v_ETA2 = sz 2;
    v_VECTOR_U_COMPRESSION_FACTOR = sz 10;
    v_VECTOR_V_COMPRESSION_FACTOR = sz 4;
}

let kyber768_generate_keypair (randomness:t_Array u8 (sz 64)):
                              (t_Array u8 (sz 2400) & t_Array u8 (sz 1184)) =
    ind_cca_generate_keypair kyber768_params randomness

let kyber768_encapsulate (public_key: t_Array u8 (sz 1184)) (randomness: t_Array u8 (sz 32)):
                         (t_Array u8 (sz 1088) & t_Array u8 (sz 32)) =
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
                               (t_Array u8 (sz 3168) & t_Array u8 (sz 1568)) =
    ind_cca_generate_keypair kyber1024_params randomness

let kyber1024_encapsulate (public_key: t_Array u8 (sz 1568)) (randomness: t_Array u8 (sz 32)):
                          (t_Array u8 (sz 1568) & t_Array u8 (sz 32)) =
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
                              (t_Array u8 (sz 1632) & t_Array u8 (sz 800))  =
    ind_cca_generate_keypair kyber512_params randomness

let kyber512_encapsulate (public_key: t_Array u8 (sz 800)) (randomness: t_Array u8 (sz 32)):
                         (t_Array u8 (sz 768) & t_Array u8 (sz 32)) =
    ind_cca_encapsulate kyber512_params public_key randomness


let kyber512_decapsulate (secret_key: t_Array u8 (sz 1632)) (ciphertext: t_Array u8 (sz 768)):
                         t_Array u8 (sz 32) =
    ind_cca_decapsulate kyber512_params secret_key ciphertext
