module Spec.MLKEM
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core

include Spec.Utils
include Spec.MLKEM.Math

(** ML-KEM Constants *)
let v_BITS_PER_COEFFICIENT: usize = sz 12

let v_COEFFICIENTS_IN_RING_ELEMENT: usize = sz 256

let v_BITS_PER_RING_ELEMENT: usize = sz 3072 // v_COEFFICIENTS_IN_RING_ELEMENT *! sz 12

let v_BYTES_PER_RING_ELEMENT: usize = sz 384 // v_BITS_PER_RING_ELEMENT /! sz 8

let v_CPA_KEY_GENERATION_SEED_SIZE: usize = sz 32

let v_H_DIGEST_SIZE: usize = sz 32 
// same as  Libcrux.Digest.digest_size (Libcrux.Digest.Algorithm_Sha3_256_ <: Libcrux.Digest.t_Algorithm)

let v_REJECTION_SAMPLING_SEED_SIZE: usize =  sz 840 // sz 168 *! sz 5

let v_SHARED_SECRET_SIZE: usize = v_H_DIGEST_SIZE

val v_ETA1 (r:rank) : u:usize{u == sz 3 \/ u == sz 2}
let v_ETA1 (r:rank) : usize = 
  if r = sz 2 then sz 3 else
  if r = sz 3 then sz 2 else
  if r = sz 4 then sz 2

let v_ETA2 (r:rank) : usize = sz 2

val v_VECTOR_U_COMPRESSION_FACTOR (r:rank) : u:usize{u == sz 10 \/ u == sz 11}
let v_VECTOR_U_COMPRESSION_FACTOR (r:rank) : usize = 
  if r = sz 2 then sz 10 else
  if r = sz 3 then sz 10 else
  if r = sz 4 then sz 11

val v_VECTOR_V_COMPRESSION_FACTOR (r:rank) : u:usize{u == sz 4 \/ u == sz 5}
let v_VECTOR_V_COMPRESSION_FACTOR (r:rank) : usize = 
  if r = sz 2 then sz 4 else
  if r = sz 3 then sz 4 else
  if r = sz 4 then sz 5

val v_ETA1_RANDOMNESS_SIZE (r:rank) : u:usize{u == sz 128 \/ u == sz 192}
let v_ETA1_RANDOMNESS_SIZE (r:rank) = v_ETA1 r *! sz 64

val v_ETA2_RANDOMNESS_SIZE (r:rank) : u:usize{u == sz 128}
let v_ETA2_RANDOMNESS_SIZE (r:rank) = v_ETA2 r *! sz 64

val v_RANKED_BYTES_PER_RING_ELEMENT (r:rank) : u:usize{u = sz 768 \/ u = sz 1152 \/ u = sz 1536}
let v_RANKED_BYTES_PER_RING_ELEMENT (r:rank)  = r *! v_BYTES_PER_RING_ELEMENT

let v_T_AS_NTT_ENCODED_SIZE (r:rank) = v_RANKED_BYTES_PER_RING_ELEMENT r
let v_CPA_PRIVATE_KEY_SIZE (r:rank) = v_RANKED_BYTES_PER_RING_ELEMENT r

val v_CPA_PUBLIC_KEY_SIZE (r:rank) : u:usize{u = sz 800 \/ u = sz 1184 \/ u = sz 1568}
let v_CPA_PUBLIC_KEY_SIZE (r:rank) = v_RANKED_BYTES_PER_RING_ELEMENT r +! sz 32

val v_CCA_PRIVATE_KEY_SIZE (r:rank) : u:usize{u = sz 1632 \/ u = sz 2400 \/ u = sz 3168}
let v_CCA_PRIVATE_KEY_SIZE (r:rank) =
  (v_CPA_PRIVATE_KEY_SIZE r +! v_CPA_PUBLIC_KEY_SIZE r +! v_H_DIGEST_SIZE +! v_SHARED_SECRET_SIZE)

let v_CCA_PUBLIC_KEY_SIZE (r:rank) = v_CPA_PUBLIC_KEY_SIZE r

val v_C1_BLOCK_SIZE (r:rank): u:usize{(u = sz 320 \/ u = sz 352) /\ v u == 32 * v (v_VECTOR_U_COMPRESSION_FACTOR r)}
let v_C1_BLOCK_SIZE (r:rank) = sz 32 *! v_VECTOR_U_COMPRESSION_FACTOR r

val v_C1_SIZE (r:rank) : u:usize{(u >=. sz 640 /\ u <=. sz 1448) /\ 
                                    v u == v (v_C1_BLOCK_SIZE r) * v r}
let v_C1_SIZE (r:rank) = v_C1_BLOCK_SIZE r *! r

val v_C2_SIZE (r:rank) : u:usize{(u = sz 128 \/ u = sz 160) /\ v u == 32 * v (v_VECTOR_V_COMPRESSION_FACTOR r)}
let v_C2_SIZE (r:rank) = sz 32 *! v_VECTOR_V_COMPRESSION_FACTOR r

val v_CPA_CIPHERTEXT_SIZE (r:rank) : u:usize {v u = v (v_C1_SIZE r) + v (v_C2_SIZE r)}
let v_CPA_CIPHERTEXT_SIZE (r:rank) = v_C1_SIZE r +! v_C2_SIZE r

let v_CCA_CIPHERTEXT_SIZE (r:rank) = v_CPA_CIPHERTEXT_SIZE r

val v_IMPLICIT_REJECTION_HASH_INPUT_SIZE (r:rank): u:usize{v u == v v_SHARED_SECRET_SIZE + 
                                                                    v (v_CPA_CIPHERTEXT_SIZE r)}
let v_IMPLICIT_REJECTION_HASH_INPUT_SIZE (r:rank) =
    v_SHARED_SECRET_SIZE +! v_CPA_CIPHERTEXT_SIZE r

val v_KEY_GENERATION_SEED_SIZE: u:usize{u = sz 64}
let v_KEY_GENERATION_SEED_SIZE: usize =
  v_CPA_KEY_GENERATION_SEED_SIZE +!
  v_SHARED_SECRET_SIZE


(** ML-KEM Types *)

type t_MLKEMPublicKey (r:rank) = t_Array u8 (v_CPA_PUBLIC_KEY_SIZE r)
type t_MLKEMPrivateKey (r:rank) = t_Array u8 (v_CCA_PRIVATE_KEY_SIZE r)
type t_MLKEMKeyPair (r:rank) = t_MLKEMPrivateKey r & t_MLKEMPublicKey r

type t_MLKEMCPAPrivateKey (r:rank) = t_Array u8 (v_CPA_PRIVATE_KEY_SIZE r)
type t_MLKEMCPAKeyPair (r:rank) = t_MLKEMCPAPrivateKey r & t_MLKEMPublicKey r

type t_MLKEMCiphertext (r:rank) = t_Array u8 (v_CPA_CIPHERTEXT_SIZE r)
type t_MLKEMSharedSecret = t_Array u8 (v_SHARED_SECRET_SIZE)


assume val sample_max: n:usize{v n < pow2 32 /\ v n >= 128 * 3 /\ v n % 3 = 0}

val sample_polynomial_ntt: seed:t_Array u8 (sz 34) -> (polynomial & bool)
let sample_polynomial_ntt seed =
  let randomness = v_XOF sample_max seed in
  let bv = bytes_to_bits randomness in
  assert (v sample_max * 8 == (((v sample_max / 3) * 2) * 12));
  let bv: bit_vec ((v (sz ((v sample_max / 3) * 2))) * 12) = retype_bit_vector bv in
  let i16s = bit_vec_to_nat_array #(sz ((v sample_max / 3) * 2)) 12 bv in
  assert ((v sample_max / 3) * 2 >= 256);
  let poly0: polynomial = Seq.create 256 0 in
  let index_t = n:nat{n <= 256} in
  let (sampled, poly1) =
    repeati #(index_t & polynomial) (sz ((v sample_max / 3) * 2))
      (fun i (sampled,acc) ->
        if sampled < 256 then
          let sample = Seq.index i16s (v i) in 
          if sample < 3329 then
             (sampled+1, Rust_primitives.Hax.update_at acc (sz sampled) sample)
          else (sampled, acc)
        else (sampled, acc))
      (0,poly0) in
  if sampled < 256 then poly0, false else poly1, true

let sample_polynomial_ntt_at_index (seed:t_Array u8 (sz 32)) (i j: (x:usize{v x <= 4})) : polynomial & bool =
    let seed34 = Seq.append seed (Seq.create 2 0uy) in
    let seed34 = Rust_primitives.Hax.update_at seed34 (sz 32) (mk_int #u8_inttype (v i)) in
    let seed34 = Rust_primitives.Hax.update_at seed34 (sz 33) (mk_int #u8_inttype (v j)) in
    sample_polynomial_ntt seed34

val sample_matrix_A_ntt: #r:rank -> seed:t_Array u8 (sz 32) -> (matrix r & bool)
let sample_matrix_A_ntt #r seed = 
  let m = 
    createi r (fun i -> 
      createi r (fun j ->
        let (p,b) = sample_polynomial_ntt_at_index seed i j in
        p))
  in 
  let sufficient_randomness = 
    repeati r (fun i b -> 
      repeati r (fun j b ->
        let (p,v) = sample_polynomial_ntt_at_index seed i j in
        b && v) b) true in
  (m, sufficient_randomness)

assume val sample_poly_cbd: v_ETA:usize{v v_ETA == 2 \/ v v_ETA == 3} -> t_Array u8 (v_ETA *! sz 64) -> polynomial

open Rust_primitives.Integers

val sample_poly_cbd2: #r:rank -> seed:t_Array u8 (sz 32) -> domain_sep:usize{v domain_sep < 256} -> polynomial
let sample_poly_cbd2 #r seed domain_sep =
  let prf_input = Seq.append seed (Seq.create 1 (mk_int #u8_inttype (v domain_sep))) in
  let prf_output = v_PRF (v_ETA2_RANDOMNESS_SIZE r) prf_input in
  sample_poly_cbd (v_ETA2 r) prf_output

val sample_poly_cbd1: #r:rank -> seed:t_Array u8 (sz 32) -> domain_sep:usize{v domain_sep < 256} -> polynomial
let sample_poly_cbd1 #r seed domain_sep =
  let prf_input = Seq.append seed (Seq.create 1 (mk_int #u8_inttype (v domain_sep))) in
  let prf_output = v_PRF (v_ETA1_RANDOMNESS_SIZE r) prf_input in
  sample_poly_cbd (v_ETA1 r) prf_output

let sample_vector_cbd1 (#r:rank) (seed:t_Array u8 (sz 32)) (domain_sep:usize{v domain_sep < 2 * v r}) : vector r =
    createi r (fun i ->  sample_poly_cbd1 #r seed (domain_sep +! i))

let sample_vector_cbd2 (#r:rank) (seed:t_Array u8 (sz 32)) (domain_sep:usize{v domain_sep < 2 * v r}) : vector r =
    createi r (fun i ->  sample_poly_cbd2 #r seed (domain_sep +! i))

let sample_vector_cbd_then_ntt (#r:rank) (seed:t_Array u8 (sz 32)) (domain_sep:usize{v domain_sep < 2 * v r}) : vector r =
    vector_ntt (sample_vector_cbd1 #r seed domain_sep)

let vector_encode_12 (#r:rank) (v: vector r) : t_Array u8 (v_T_AS_NTT_ENCODED_SIZE r)
  = let s: t_Array (t_Array _ (sz 384)) r = map_array (byte_encode 12) (coerce_vector_12 v) in
    flatten s

let vector_decode_12 (#r:rank) (arr: t_Array u8 (v_T_AS_NTT_ENCODED_SIZE r)): vector r
  = createi r (fun block -> 
      let block_size = (sz (32 * 12)) in
      let slice = Seq.slice arr (v block * v block_size) 
                                (v block * v block_size + v block_size) in
      byte_decode 12 slice
    )

let compress_then_encode_message (p:polynomial) : t_Array u8 v_SHARED_SECRET_SIZE
  = compress_then_byte_encode 1 p

let decode_then_decompress_message (b:t_Array u8 v_SHARED_SECRET_SIZE): polynomial
  = byte_decode_then_decompress 1 b

let compress_then_encode_u (#r:rank) (vec: vector r): t_Array u8 (v_C1_SIZE r)
  = let d = v (v_VECTOR_U_COMPRESSION_FACTOR r) in
    flatten (map_array (compress_then_byte_encode d) vec)

let decode_then_decompress_u (#r:rank) (arr: t_Array u8 (v_C1_SIZE r)): vector r
  = let d = v_VECTOR_U_COMPRESSION_FACTOR r in
    createi r (fun block -> 
      let block_size = v_C1_BLOCK_SIZE r in
      let slice = Seq.slice arr (v block * v block_size) 
                                (v block * v block_size + v block_size) in
      byte_decode_then_decompress (v d) slice
    )

let compress_then_encode_v (#r:rank): polynomial -> t_Array u8 (v_C2_SIZE r)
  = compress_then_byte_encode (v (v_VECTOR_V_COMPRESSION_FACTOR r))

let decode_then_decompress_v (#r:rank): t_Array u8 (v_C2_SIZE r) -> polynomial
  = byte_decode_then_decompress (v (v_VECTOR_V_COMPRESSION_FACTOR r)) 

(** IND-CPA Functions *)

/// This function implements most of <strong>Algorithm 12</strong> of the
/// NIST FIPS 203 specification; this is the MLKEM CPA-PKE key generation algorithm.
///
/// We say "most of" since Algorithm 12 samples the required randomness within
/// the function itself, whereas this implementation expects it to be provided
/// through the `key_generation_seed` parameter.

val ind_cpa_generate_keypair (r:rank) (randomness:t_Array u8 v_CPA_KEY_GENERATION_SEED_SIZE) :
                             (t_MLKEMCPAKeyPair r & bool)
let ind_cpa_generate_keypair r randomness =
    let hashed = v_G randomness in
    let (seed_for_A, seed_for_secret_and_error) = split hashed (sz 32) in
    let (matrix_A_as_ntt, sufficient_randomness) = sample_matrix_A_ntt #r seed_for_A in
    let secret_as_ntt = sample_vector_cbd_then_ntt #r seed_for_secret_and_error (sz 0) in
    let error_as_ntt = sample_vector_cbd_then_ntt #r seed_for_secret_and_error r in
    let t_as_ntt = compute_As_plus_e_ntt #r matrix_A_as_ntt secret_as_ntt error_as_ntt in
    let public_key_serialized = Seq.append (vector_encode_12 #r t_as_ntt) seed_for_A in
    let secret_key_serialized = vector_encode_12 #r secret_as_ntt in
    ((secret_key_serialized,public_key_serialized), sufficient_randomness)

/// This function implements <strong>Algorithm 13</strong> of the
/// NIST FIPS 203 specification; this is the MLKEM CPA-PKE encryption algorithm.

val ind_cpa_encrypt (r:rank) (public_key: t_MLKEMPublicKey r)
                    (message: t_Array u8 v_SHARED_SECRET_SIZE)
                    (randomness:t_Array u8 v_SHARED_SECRET_SIZE) :
                    (t_MLKEMCiphertext r & bool)
    
let ind_cpa_encrypt r public_key message randomness =
    let (t_as_ntt_bytes, seed_for_A) = split public_key (v_T_AS_NTT_ENCODED_SIZE r) in
    let t_as_ntt = vector_decode_12 #r t_as_ntt_bytes in 
    let matrix_A_as_ntt, sufficient_randomness = sample_matrix_A_ntt #r seed_for_A in
    let r_as_ntt = sample_vector_cbd_then_ntt #r randomness (sz 0) in
    let error_1 = sample_vector_cbd2 #r randomness r in
    let error_2 = sample_poly_cbd2 #r randomness (r +! r) in
    let u = vector_add (vector_inv_ntt (matrix_vector_mul_ntt (matrix_transpose matrix_A_as_ntt) r_as_ntt)) error_1 in
    let mu = decode_then_decompress_message message in
    let v = poly_add (poly_add (vector_dot_product_ntt t_as_ntt r_as_ntt) error_2) mu in  
    let c1 = compress_then_encode_u #r u in
    let c2 = compress_then_encode_v #r v in
    (concat c1 c2, sufficient_randomness)

/// This function implements <strong>Algorithm 14</strong> of the
/// NIST FIPS 203 specification; this is the MLKEM CPA-PKE decryption algorithm.

val ind_cpa_decrypt (r:rank) (secret_key: t_MLKEMCPAPrivateKey r)
                    (ciphertext: t_MLKEMCiphertext r): 
                    t_MLKEMSharedSecret

let ind_cpa_decrypt r secret_key ciphertext =
    let (c1,c2) = split ciphertext (v_C1_SIZE r) in
    let u = decode_then_decompress_u #r c1 in
    let v = decode_then_decompress_v #r c2 in
    let secret_as_ntt = vector_decode_12 #r secret_key in
    let w = poly_sub v (poly_inv_ntt (vector_dot_product_ntt secret_as_ntt (vector_ntt u))) in
    compress_then_encode_message w

(** IND-CCA Functions *)


/// This function implements most of Algorithm 15 of the
/// NIST FIPS 203 specification; this is the MLKEM CCA-KEM key generation algorithm.
///
/// We say "most of" since Algorithm 15 samples the required randomness within
/// the function itself, whereas this implementation expects it to be provided
/// through the `randomness` parameter.
/// 
/// TODO: input validation

val ind_cca_generate_keypair (r:rank) (randomness:t_Array u8 v_KEY_GENERATION_SEED_SIZE) :
                             t_MLKEMKeyPair r & bool
let ind_cca_generate_keypair p randomness =
    let (ind_cpa_keypair_randomness, implicit_rejection_value) =
        split randomness v_CPA_KEY_GENERATION_SEED_SIZE in
        
    let (ind_cpa_secret_key,ind_cpa_public_key), sufficient_randomness = ind_cpa_generate_keypair p ind_cpa_keypair_randomness in
    let ind_cca_secret_key = Seq.append ind_cpa_secret_key (
                             Seq.append ind_cpa_public_key (
                             Seq.append (v_H ind_cpa_public_key) implicit_rejection_value)) in
    (ind_cca_secret_key, ind_cpa_public_key), sufficient_randomness

/// This function implements most of Algorithm 16 of the
/// NIST FIPS 203 specification; this is the MLKEM CCA-KEM encapsulation algorithm.
///
/// We say "most of" since Algorithm 16 samples the required randomness within
/// the function itself, whereas this implementation expects it to be provided
/// through the `randomness` parameter.
///
/// TODO: input validation

val ind_cca_encapsulate (r:rank) (public_key: t_MLKEMPublicKey r)
                        (randomness:t_Array u8 v_SHARED_SECRET_SIZE) :
                        (t_MLKEMCiphertext r &  t_MLKEMSharedSecret) & bool
let ind_cca_encapsulate p public_key randomness =
    let to_hash = concat randomness (v_H public_key) in
    let hashed = v_G to_hash in
    let (shared_secret, pseudorandomness) = split hashed v_SHARED_SECRET_SIZE in
    let ciphertext, sufficient_randomness = ind_cpa_encrypt p public_key randomness pseudorandomness in
    (ciphertext,shared_secret), sufficient_randomness
    

/// This function implements Algorithm 17 of the
/// NIST FIPS 203 specification; this is the MLKEM CCA-KEM encapsulation algorithm.

val ind_cca_decapsulate (r:rank) (secret_key: t_MLKEMPrivateKey r)
                        (ciphertext: t_MLKEMCiphertext r): 
                         t_MLKEMSharedSecret & bool
let ind_cca_decapsulate p secret_key ciphertext =
    let (ind_cpa_secret_key,rest) = split secret_key (v_CPA_PRIVATE_KEY_SIZE p) in
    let (ind_cpa_public_key,rest) = split rest (v_CPA_PUBLIC_KEY_SIZE p) in
    let (ind_cpa_public_key_hash,implicit_rejection_value) = split rest v_H_DIGEST_SIZE in
    
    let decrypted = ind_cpa_decrypt p ind_cpa_secret_key ciphertext in
    let to_hash = concat decrypted ind_cpa_public_key_hash in
    let hashed = v_G to_hash in
    let (success_shared_secret, pseudorandomness) = split hashed v_SHARED_SECRET_SIZE in

    assert (Seq.length implicit_rejection_value = 32);
    let to_hash = concat implicit_rejection_value ciphertext in
    let rejection_shared_secret = v_J to_hash in

    let reencrypted, sufficient_randomness = ind_cpa_encrypt p ind_cpa_public_key decrypted pseudorandomness in
    if reencrypted = ciphertext
    then success_shared_secret, sufficient_randomness
    else rejection_shared_secret, sufficient_randomness
   
