module Spec.MLKEM
#set-options "--fuel 0 --ifuel 1 --z3rlimit 200"
open FStar.Mul
open Core
open Spec.Utils

(** ML-KEM Constants *)
let v_BITS_PER_COEFFICIENT: usize = sz 12

let v_COEFFICIENTS_IN_RING_ELEMENT: usize = sz 256

let v_BITS_PER_RING_ELEMENT: usize = sz 3072 // v_COEFFICIENTS_IN_RING_ELEMENT *! sz 12

let v_BYTES_PER_RING_ELEMENT: usize = sz 384 // v_BITS_PER_RING_ELEMENT /! sz 8

let v_CPA_KEY_GENERATION_SEED_SIZE: usize = sz 32

let v_FIELD_MODULUS: i32 = 3329l

let v_H_DIGEST_SIZE: usize = sz 32 
// same as  Libcrux.Digest.digest_size (Libcrux.Digest.Algorithm_Sha3_256_ <: Libcrux.Digest.t_Algorithm)

let v_REJECTION_SAMPLING_SEED_SIZE: usize =  sz 840 // sz 168 *! sz 5

let v_SHARED_SECRET_SIZE: usize = v_H_DIGEST_SIZE

let is_rank (r:usize) =
  r == sz 2 \/ r == sz 3 \/ r == sz 4

type rank = r:usize{is_rank r}

let v_ETA1 (r:rank) : usize = 
  if r = sz 2 then sz 3 else
  if r = sz 3 then sz 2 else
  if r = sz 4 then sz 2

let v_ETA2 (r:rank) : usize = sz 2

let v_VECTOR_U_COMPRESSION_FACTOR (r:rank) : usize = 
  if r = sz 2 then sz 10 else
  if r = sz 3 then sz 10 else
  if r = sz 4 then sz 11

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

(** MLKEM Math and Sampling *)

type field_element = n:nat{n < v v_FIELD_MODULUS}
type polynomial (ntt:bool) = t_Array field_element (sz 256)
type vector (r:rank) (ntt:bool) = t_Array (polynomial ntt) r
type matrix (r:rank) (ntt:bool) = t_Array (vector r ntt) r

val field_add: field_element -> field_element -> field_element
let field_add a b = (a + b) % v v_FIELD_MODULUS

val field_sub: field_element -> field_element -> field_element
let field_sub a b = (a - b) % v v_FIELD_MODULUS

val field_neg: field_element -> field_element
let field_neg a = (0 - a) % v v_FIELD_MODULUS

val field_mul: field_element -> field_element -> field_element
let field_mul a b = (a * b) % v v_FIELD_MODULUS

val poly_add: #ntt:bool -> polynomial ntt -> polynomial ntt -> polynomial ntt
let poly_add a b = map2 field_add a b

val poly_sub: #ntt:bool -> polynomial ntt -> polynomial ntt -> polynomial ntt
let poly_sub a b = map2 field_sub a b


(*
bitrev7 = [int('{:07b}'.format(x)[::-1], 2) for x in range(0,128)]
zetas = [pow(17,x) % 3329 for x in bitrev7]
zetas_mont = [pow(2,16) * x % 3329 for x in zetas]
zetas_mont_r = [(x - 3329 if x > 1664 else x) for x in zetas_mont]

bitrev7 is 
[0, 64, 32, 96, 16, 80, 48, 112, 8, 72, 40, 104, 24, 88, 56, 120, 4, 68, 36, 100, 20, 84, 52, 116, 12, 76, 44, 108, 28, 92, 60, 124, 2, 66, 34, 98, 18, 82, 50, 114, 10, 74, 42, 106, 26, 90, 58, 122, 6, 70, 38, 102, 22, 86, 54, 118, 14, 78, 46, 110, 30, 94, 62, 126, 1, 65, 33, 97, 17, 81, 49, 113, 9, 73, 41, 105, 25, 89, 57, 121, 5, 69, 37, 101, 21, 85, 53, 117, 13, 77, 45, 109, 29, 93, 61, 125, 3, 67, 35, 99, 19, 83, 51, 115, 11, 75, 43, 107, 27, 91, 59, 123, 7, 71, 39, 103, 23, 87, 55, 119, 15, 79, 47, 111, 31, 95, 63, 127]

zetas = 17^bitrev7 is
[1, 1729, 2580, 3289, 2642, 630, 1897, 848, 1062, 1919, 193, 797, 2786, 3260, 569, 1746, 296, 2447, 1339, 1476, 3046, 56, 2240, 1333, 1426, 2094, 535, 2882, 2393, 2879, 1974, 821, 289, 331, 3253, 1756, 1197, 2304, 2277, 2055, 650, 1977, 2513, 632, 2865, 33, 1320, 1915, 2319, 1435, 807, 452, 1438, 2868, 1534, 2402, 2647, 2617, 1481, 648, 2474, 3110, 1227, 910, 17, 2761, 583, 2649, 1637, 723, 2288, 1100, 1409, 2662, 3281, 233, 756, 2156, 3015, 3050, 1703, 1651, 2789, 1789, 1847, 952, 1461, 2687, 939, 2308, 2437, 2388, 733, 2337, 268, 641, 1584, 2298, 2037, 3220, 375, 2549, 2090, 1645, 1063, 319, 2773, 757, 2099, 561, 2466, 2594, 2804, 1092, 403, 1026, 1143, 2150, 2775, 886, 1722, 1212, 1874, 1029, 2110, 2935, 885, 2154]

zetas_mont = zetas * 2^16 is
[2285, 2571, 2970, 1812, 1493, 1422, 287, 202, 3158, 622, 1577, 182, 962, 2127, 1855, 1468, 573, 2004, 264, 383, 2500, 1458, 1727, 3199, 2648, 1017, 732, 608, 1787, 411, 3124, 1758, 1223, 652, 2777, 1015, 2036, 1491, 3047, 1785, 516, 3321, 3009, 2663, 1711, 2167, 126, 1469, 2476, 3239, 3058, 830, 107, 1908, 3082, 2378, 2931, 961, 1821, 2604, 448, 2264, 677, 2054, 2226, 430, 555, 843, 2078, 871, 1550, 105, 422, 587, 177, 3094, 3038, 2869, 1574, 1653, 3083, 778, 1159, 3182, 2552, 1483, 2727, 1119, 1739, 644, 2457, 349, 418, 329, 3173, 3254, 817, 1097, 603, 610, 1322, 2044, 1864, 384, 2114, 3193, 1218, 1994, 2455, 220, 2142, 1670, 2144, 1799, 2051, 794, 1819, 2475, 2459, 478, 3221, 3021, 996, 991, 958, 1869, 1522, 1628]

zetas_mont_r = zetas_mont - 3329 if zetas_mont > 1664 else zetas_mont is
[-1044, -758, -359, -1517, 1493, 1422, 287, 202, -171, 622, 1577, 182, 962, -1202, -1474, 1468, 573, -1325, 264, 383, -829, 1458, -1602, -130, -681, 1017, 732, 608, -1542, 411, -205, -1571, 1223, 652, -552, 1015, -1293, 1491, -282, -1544, 516, -8, -320, -666, -1618, -1162, 126, 1469, -853, -90, -271, 830, 107, -1421, -247, -951, -398, 961, -1508, -725, 448, -1065, 677, -1275, -1103, 430, 555, 843, -1251, 871, 1550, 105, 422, 587, 177, -235, -291, -460, 1574, 1653, -246, 778, 1159, -147, -777, 1483, -602, 1119, -1590, 644, -872, 349, 418, 329, -156, -75, 817, 1097, 603, 610, 1322, -1285, -1465, 384, -1215, -136, 1218, -1335, -874, 220, -1187, -1659, -1185, -1530, -1278, 794, -1510, -854, -870, 478, -108, -308, 996, 991, 958, -1460, 1522, 1628]
*)

let zetas_list : list field_element = [1; 1729; 2580; 3289; 2642; 630; 1897; 848; 1062; 1919; 193; 797; 2786; 3260; 569; 1746; 296; 2447; 1339; 1476; 3046; 56; 2240; 1333; 1426; 2094; 535; 2882; 2393; 2879; 1974; 821; 289; 331; 3253; 1756; 1197; 2304; 2277; 2055; 650; 1977; 2513; 632; 2865; 33; 1320; 1915; 2319; 1435; 807; 452; 1438; 2868; 1534; 2402; 2647; 2617; 1481; 648; 2474; 3110; 1227; 910; 17; 2761; 583; 2649; 1637; 723; 2288; 1100; 1409; 2662; 3281; 233; 756; 2156; 3015; 3050; 1703; 1651; 2789; 1789; 1847; 952; 1461; 2687; 939; 2308; 2437; 2388; 733; 2337; 268; 641; 1584; 2298; 2037; 3220; 375; 2549; 2090; 1645; 1063; 319; 2773; 757; 2099; 561; 2466; 2594; 2804; 1092; 403; 1026; 1143; 2150; 2775; 886; 1722; 1212; 1874; 1029; 2110; 2935; 885; 2154]

let zetas : t_Array field_element (sz 128) = 
  assert_norm(List.Tot.length zetas_list == 128);
  Rust_primitives.Arrays.of_list zetas_list
  
let poly_ntt_step (a:field_element) (b:field_element) (i:nat{i < 128}) =
  let t = field_mul b zetas.[sz i] in
  let b = field_sub a t in
  let a = field_add a t in
  (a,b)

let poly_ntt_layer #b (p:polynomial b) (l:nat{l > 0 /\ l < 8}) : polynomial b =
  let len = pow2 l in
  let k = (128 / len) - 1 in
  Rust_primitives.Arrays.createi (sz 256) (fun i ->
    let round = v i / (2 * len) in
    let idx = v i % (2 * len) in
    let (idx0, idx1) = if idx < len then (idx, idx+len) else (idx-len,idx) in
    let (a_ntt, b_ntt) = poly_ntt_step p.[sz idx0] p.[sz idx1] (round + k) in
    if idx < len then a_ntt else b_ntt)

val poly_ntt: polynomial false -> polynomial true
let poly_ntt p =
  let p = poly_ntt_layer p 7 in
  let p = poly_ntt_layer p 6 in
  let p = poly_ntt_layer p 5 in
  let p = poly_ntt_layer p 4 in
  let p = poly_ntt_layer p 3 in
  let p = poly_ntt_layer p 2 in
  let p = poly_ntt_layer p 1 in
  p

let poly_inv_ntt_step (a:field_element) (b:field_element) (i:nat{i < 128}) =
  let b_minus_a = field_sub b a in
  let a = field_add a b in
  let b = field_mul b_minus_a zetas.[sz i] in
  (a,b)

let poly_inv_ntt_layer #b (p:polynomial b) (l:nat{l > 0 /\ l < 8}) : polynomial b =
  let len = pow2 l in
  let k = (256 / len) - 1 in
  Rust_primitives.Arrays.createi (sz 256) (fun i ->
    let round = v i / (2 * len) in
    let idx = v i % (2 * len) in
    let (idx0, idx1) = if idx < len then (idx, idx+len) else (idx-len,idx) in
    let (a_ntt, b_ntt) = poly_inv_ntt_step p.[sz idx0] p.[sz idx1] (k - round) in
    if idx < len then a_ntt else b_ntt)

val poly_inv_ntt: polynomial true -> polynomial false
let poly_inv_ntt p =
  let p = poly_inv_ntt_layer p 1 in
  let p = poly_inv_ntt_layer p 2 in
  let p = poly_inv_ntt_layer p 3 in
  let p = poly_inv_ntt_layer p 4 in
  let p = poly_inv_ntt_layer p 5 in
  let p = poly_inv_ntt_layer p 6 in
  let p = poly_inv_ntt_layer p 7 in
  p

let poly_base_case_multiply (a0 a1 b0 b1 zeta:field_element) =
  let c0 = field_add (field_mul a0 b0) (field_mul (field_mul a1 b1) zeta) in
  let c1 = field_add (field_mul a0 b1) (field_mul a1 b0) in
  (c0,c1)

val poly_mul_ntt: polynomial true -> polynomial true -> polynomial true
let poly_mul_ntt a b =
  Rust_primitives.Arrays.createi (sz 256) (fun i ->
    let a0 = a.[sz (2 * (v i / 2))] in
    let a1 = a.[sz (2 * (v i / 2) + 1)] in
    let b0 = b.[sz (2 * (v i / 2))] in
    let b1 = b.[sz (2 * (v i / 2) + 1)] in
    let zeta_4 = zetas.[sz (64 + (v i/4))] in
    let zeta = if v i % 4 < 2 then zeta_4 else field_neg zeta_4 in
    let (c0,c1) = poly_base_case_multiply a0 a1 b0 b1 zeta in
    if v i % 2 = 0 then c0 else c1)
  

val vector_add: #r:rank -> #ntt:bool -> vector r ntt -> vector r ntt -> vector r ntt
let vector_add #p a b = map2 poly_add a b

val vector_ntt: #r:rank -> vector r false -> vector r true
let vector_ntt #p v = map_array poly_ntt v

val vector_inv_ntt: #r:rank -> vector r true -> vector r false
let vector_inv_ntt #p v = map_array poly_inv_ntt v

val vector_mul_ntt: #r:rank -> vector r true  -> vector r true -> vector r true
let vector_mul_ntt #p a b = map2 poly_mul_ntt a b

val vector_sum: #r:rank -> #ntt:bool -> vector r ntt -> polynomial ntt
let vector_sum #r a = repeati (v r - 1)
     (fun i x -> poly_add x (Lib.Sequence.index #_ #(v r) a (i+1))) (Lib.Sequence.index #_ #(v r) a 0)

val vector_dot_product_ntt: #r:rank -> vector r true -> vector r true -> polynomial true
let vector_dot_product_ntt a b = vector_sum (vector_mul_ntt a b)

val matrix_transpose: #r:rank -> #ntt:bool -> matrix r ntt -> matrix r ntt
let matrix_transpose #r m =
  createi r (fun i -> 
    createi r (fun j ->
      m.[j].[i]))

val matrix_vector_mul_ntt: #r:rank -> matrix r true -> vector r true -> vector r true
let matrix_vector_mul_ntt #r m v =
  createi r (fun i -> vector_dot_product_ntt m.[i] v)

val compute_As_plus_e_ntt: #r:rank -> a:matrix r true -> s:vector r true -> e:vector r true -> vector r true
let compute_As_plus_e_ntt #p a s e = vector_add (matrix_vector_mul_ntt a s) e

let bits_to_bytes (#bytes: usize) (bv: bit_vec (v bytes * 8))
  : Pure (t_Array u8 bytes)
         (requires True)
         (ensures fun r -> (forall i. bit_vec_of_int_t_array r 8 i == bv i))
  = bit_vec_to_int_t_array 8 bv

let bytes_to_bits (#bytes: usize) (r: t_Array u8 bytes)
  : Pure (i: bit_vec (v bytes * 8))
         (requires True)
         (ensures fun f -> (forall i. bit_vec_of_int_t_array r 8 i == f i))
  = bit_vec_of_int_t_array r 8

unfold let retype_bit_vector #a #b (#_:unit{a == b}) (x: a): b = x


// note we take seed of size 32 not 34 as in hacspec
assume val sample_matrix_A_ntt: #r:rank -> seed:t_Array u8 (sz 32) -> matrix r true
// note we take seed of size 32 not 33 as in hacspec
assume val sample_vector_cbd: #r:rank -> seed:t_Array u8 (sz 32) -> domain_sep:usize -> vector r false
// note we take seed of size 32 not 33 as in hacspec

assume val sample_poly_binomial: v_ETA:usize{v v_ETA <= 3}  -> t_Array u8 (v_ETA *! sz 64) -> polynomial false

open Rust_primitives.Integers

val sample_poly_cbd: #r:rank -> seed:t_Array u8 (sz 32) -> domain_sep:usize{v domain_sep < 256} -> polynomial false
let sample_poly_cbd #r seed domain_sep =
  let prf_input = Seq.append seed (Seq.create 1 (mk_int #u8_inttype (v domain_sep))) in
  let prf_output = v_PRF (v_ETA2_RANDOMNESS_SIZE r) prf_input in
  sample_poly_binomial (v_ETA2 r) prf_output

let sample_vector_cbd_then_ntt (#r:rank) (seed:t_Array u8 (sz 32)) (domain_sep:usize) : vector r true =
    vector_ntt (sample_vector_cbd #r seed domain_sep)

type dT = d: nat {d = 1 \/ d = 4 \/ d = 5 \/ d = 10 \/ d = 11 \/ d = 12}
let max_d (d:dT) = if d < 12 then pow2 d else v v_FIELD_MODULUS
type field_element_d (d:dT) = n:nat{n < max_d d}
type polynomial_d (d:dT) = t_Array (field_element_d d) (sz 256)
type vector_d (r:rank) (d:dT) = t_Array (polynomial_d d) r


let compress_d (d: dT {d <> 12}) (x: field_element): field_element_d d
  = let r = (pow2 d * x + 1664) / v v_FIELD_MODULUS in
    assume (r * v v_FIELD_MODULUS < pow2 d * x + 1664);
    assume (pow2 d * x + 1664 < pow2 d * v v_FIELD_MODULUS + 1664);
    assume (r < pow2 d);
    r

let decompress_d (d: dT {d <> 12}) (x: field_element_d d): field_element
  = let r = (x * v v_FIELD_MODULUS + 1664) / pow2 d in
    assume (r < v v_FIELD_MODULUS);
    r
    

let byte_encode (d: dT) (coefficients: polynomial_d d): t_Array u8 (sz (32 * d))
  =  let coefficients' : t_Array nat (sz 256) = map_array #(field_element_d d) (fun x -> x <: nat) coefficients in
     bits_to_bytes #(sz (32 * d))
       (retype_bit_vector (bit_vec_of_nat_array coefficients' d))

let byte_decode (d: dT) (coefficients: t_Array u8 (sz (32 * d))): polynomial_d d
  = let bv = bytes_to_bits coefficients in
    let arr: t_Array nat (sz 256) = bit_vec_to_nat_array d (retype_bit_vector bv) in
    let p = map_array (fun (x: nat) -> x % v v_FIELD_MODULUS) arr in
    introduce forall i. (d < 12 ==> Seq.index p i < pow2 d)
    with assert (Seq.index p i == Seq.index p (v (sz i)));
    introduce forall i. (d == 12 ==> Seq.index p i < v v_FIELD_MODULUS)
    with assert (Seq.index p i == Seq.index p (v (sz i)));
    assert (forall i. (d < 12 ==> Seq.index p i < pow2 d) /\ (d == 12 ==> Seq.index p i < v v_FIELD_MODULUS));
    admit();
    p

let coerce_polynomial_12 #ntt (p:polynomial ntt): polynomial_d 12 = p
let coerce_vector_12 #ntt (#r:rank) (v:vector r ntt): vector_d r 12 = v

let vector_encode_12 (#r:rank) (#ntt:bool) (v: vector r ntt): t_Array u8 (v_T_AS_NTT_ENCODED_SIZE r)
  = let s: t_Array (t_Array _ (sz 384)) r = map_array (byte_encode 12) (coerce_vector_12 v) in
    flatten s

let vector_decode_12 (#r:rank) (#ntt:bool) (arr: t_Array u8 (v_T_AS_NTT_ENCODED_SIZE r)): vector r ntt
  = createi r (fun block -> 
      let block_size = (sz (32 * 12)) in
      let slice = Seq.slice arr (v block * v block_size) 
                                (v block * v block_size + v block_size) in
      byte_decode 12 slice
    )

let compress_then_byte_encode #ntt (d: dT {d <> 12}) (coefficients: polynomial ntt): t_Array u8 (sz (32 * d))
  = let coefs: t_Array (field_element_d d) (sz 256) = map_array (compress_d d) coefficients
    in
    byte_encode d coefs

let byte_decode_then_decompress #ntt (d: dT {d <> 12}) (b:t_Array u8 (sz (32 * d))): polynomial ntt
  = map_array (decompress_d d) (byte_decode d b)

let compress_then_encode_message #ntt (p:polynomial ntt) : t_Array u8 v_SHARED_SECRET_SIZE
  = compress_then_byte_encode 1 p

let decode_then_decompress_message #ntt (b:t_Array u8 v_SHARED_SECRET_SIZE): polynomial ntt
  = byte_decode_then_decompress 1 b

let compress_then_encode_u (#r:rank) (#ntt:bool) (vec: vector r ntt): t_Array u8 (v_C1_SIZE r)
  = let d = v (v_VECTOR_U_COMPRESSION_FACTOR r) in
    flatten (map_array (compress_then_byte_encode d) vec)

let decode_then_decompress_u (#r:rank) (#ntt:bool) (arr: t_Array u8 (v_C1_SIZE r)): vector r ntt
  = let d = v_VECTOR_U_COMPRESSION_FACTOR r in
    createi r (fun block -> 
      let block_size = v_C1_BLOCK_SIZE r in
      let slice = Seq.slice arr (v block * v block_size) 
                                (v block * v block_size + v block_size) in
      byte_decode_then_decompress (v d) slice
    )

let compress_then_encode_v (#r:rank) (#ntt:bool): polynomial ntt -> t_Array u8 (v_C2_SIZE r)
  = compress_then_byte_encode (v (v_VECTOR_V_COMPRESSION_FACTOR r))

let decode_then_decompress_v (#r:rank) (#ntt:bool): t_Array u8 (v_C2_SIZE r) -> polynomial ntt
  = byte_decode_then_decompress (v (v_VECTOR_V_COMPRESSION_FACTOR r)) 

(** IND-CPA Functions *)

/// This function implements most of <strong>Algorithm 12</strong> of the
/// NIST FIPS 203 specification; this is the MLKEM CPA-PKE key generation algorithm.
///
/// We say "most of" since Algorithm 12 samples the required randomness within
/// the function itself, whereas this implementation expects it to be provided
/// through the `key_generation_seed` parameter.

val ind_cpa_generate_keypair (r:rank) (randomness:t_Array u8 v_CPA_KEY_GENERATION_SEED_SIZE) :
                             t_MLKEMCPAKeyPair r
let ind_cpa_generate_keypair r randomness =
    let hashed = v_G randomness in
      let (seed_for_A, seed_for_secret_and_error) = split hashed (sz 32) in
    let matrix_A_as_ntt = sample_matrix_A_ntt #r seed_for_A in
    let secret_as_ntt = sample_vector_cbd_then_ntt #r seed_for_secret_and_error (sz 0) in
    let error_as_ntt = sample_vector_cbd_then_ntt #r seed_for_secret_and_error r in
    let t_as_ntt = compute_As_plus_e_ntt #r matrix_A_as_ntt secret_as_ntt error_as_ntt in
    let public_key_serialized = Seq.append (vector_encode_12 #r t_as_ntt) seed_for_A in
    let secret_key_serialized = vector_encode_12 #r secret_as_ntt in
    (secret_key_serialized,public_key_serialized)

/// This function implements <strong>Algorithm 13</strong> of the
/// NIST FIPS 203 specification; this is the MLKEM CPA-PKE encryption algorithm.

val ind_cpa_encrypt (r:rank) (public_key: t_MLKEMPublicKey r)
                    (message: t_Array u8 v_SHARED_SECRET_SIZE)
                    (randomness:t_Array u8 v_SHARED_SECRET_SIZE) :
                    t_MLKEMCiphertext r

let ind_cpa_encrypt r public_key message randomness =
    let (t_as_ntt_bytes, seed_for_A) = split public_key (v_T_AS_NTT_ENCODED_SIZE r) in
    let t_as_ntt = vector_decode_12 #r t_as_ntt_bytes in 
    let matrix_A_as_ntt = sample_matrix_A_ntt #r seed_for_A in
    let r_as_ntt = sample_vector_cbd_then_ntt #r randomness (sz 0) in
    let error_1 = sample_vector_cbd #r randomness r in
    let error_2 = sample_poly_cbd #r randomness (r +! r) in
    let u = vector_add (vector_inv_ntt (matrix_vector_mul_ntt (matrix_transpose matrix_A_as_ntt) r_as_ntt)) error_1 in
    let mu = decode_then_decompress_message message in
    let v = poly_add (poly_add (vector_dot_product_ntt t_as_ntt r_as_ntt) error_2) mu in  
    let c1 = compress_then_encode_u #r u in
    let c2 = compress_then_encode_v #r v in
    concat c1 c2

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
    let w = poly_sub v (poly_inv_ntt #r (vector_dot_product_ntt secret_as_ntt (vector_ntt u))) in
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
                             t_MLKEMKeyPair r
let ind_cca_generate_keypair p randomness =
    let (ind_cpa_keypair_randomness, implicit_rejection_value) =
        split randomness v_CPA_KEY_GENERATION_SEED_SIZE in
        
    let (ind_cpa_secret_key,ind_cpa_public_key) = ind_cpa_generate_keypair p ind_cpa_keypair_randomness in
    let ind_cca_secret_key = Seq.append ind_cpa_secret_key (
                             Seq.append ind_cpa_public_key (
                             Seq.append (v_H ind_cpa_public_key) implicit_rejection_value)) in
    (ind_cca_secret_key, ind_cpa_public_key)

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
                        (t_MLKEMCiphertext r &  t_MLKEMSharedSecret)
let ind_cca_encapsulate p public_key randomness =
    let to_hash = concat randomness (v_H public_key) in
    let hashed = v_G to_hash in
    let (shared_secret, pseudorandomness) = split hashed v_SHARED_SECRET_SIZE in
    let ciphertext = ind_cpa_encrypt p public_key randomness pseudorandomness in
    (ciphertext,shared_secret)
    

/// This function implements Algorithm 17 of the
/// NIST FIPS 203 specification; this is the MLKEM CCA-KEM encapsulation algorithm.

val ind_cca_decapsulate (r:rank) (secret_key: t_MLKEMPrivateKey r)
                        (ciphertext: t_MLKEMCiphertext r): 
                         t_MLKEMSharedSecret
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

    let reencrypted = ind_cpa_encrypt p ind_cpa_public_key decrypted pseudorandomness in
    if reencrypted = ciphertext
    then success_shared_secret
    else rejection_shared_secret
   

(** MLKEM-768 Instantiation *)

let mlkem768_rank = sz 3

let mlkem768_generate_keypair (randomness:t_Array u8 (sz 64)):
                              (t_Array u8 (sz 2400) & t_Array u8 (sz 1184)) =
    ind_cca_generate_keypair mlkem768_rank randomness

let mlkem768_encapsulate (public_key: t_Array u8 (sz 1184)) (randomness: t_Array u8 (sz 32)):
                         (t_Array u8 (sz 1088) & t_Array u8 (sz 32)) =
    ind_cca_encapsulate mlkem768_rank public_key randomness


let mlkem768_decapsulate (secret_key: t_Array u8 (sz 2400)) (ciphertext: t_Array u8 (sz 1088)):
                         t_Array u8 (sz 32) =
    ind_cca_decapsulate mlkem768_rank secret_key ciphertext

(** MLKEM-1024 Instantiation *)

let mlkem1024_rank = sz 4

let mlkem1024_generate_keypair (randomness:t_Array u8 (sz 64)):
                               (t_Array u8 (sz 3168) & t_Array u8 (sz 1568)) =
    ind_cca_generate_keypair mlkem1024_rank randomness

let mlkem1024_encapsulate (public_key: t_Array u8 (sz 1568)) (randomness: t_Array u8 (sz 32)):
                          (t_Array u8 (sz 1568) & t_Array u8 (sz 32)) =
    ind_cca_encapsulate mlkem1024_rank public_key randomness


let mlkem1024_decapsulate (secret_key: t_Array u8 (sz 3168)) (ciphertext: t_Array u8 (sz 1568)):
                           t_Array u8 (sz 32) =
    ind_cca_decapsulate mlkem1024_rank secret_key ciphertext

(** MLKEM-512 Instantiation *)

let mlkem512_rank : rank = sz 2

let mlkem512_generate_keypair (randomness:t_Array u8 (sz 64)):
                              (t_Array u8 (sz 1632) & t_Array u8 (sz 800))  =
    ind_cca_generate_keypair mlkem512_rank randomness

let mlkem512_encapsulate (public_key: t_Array u8 (sz 800)) (randomness: t_Array u8 (sz 32)):
                         (t_Array u8 (sz 768) & t_Array u8 (sz 32)) =
    ind_cca_encapsulate mlkem512_rank public_key randomness


let mlkem512_decapsulate (secret_key: t_Array u8 (sz 1632)) (ciphertext: t_Array u8 (sz 768)):
                         t_Array u8 (sz 32) =
    ind_cca_decapsulate mlkem512_rank secret_key ciphertext
