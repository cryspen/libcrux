module Spec.MLKEM.Math
#set-options "--fuel 0 --ifuel 1 --z3rlimit 30"

open FStar.Mul
open Core
open Spec.Utils

let v_FIELD_MODULUS: i32 = 3329l
let is_rank (r:usize) = v r == 2 \/ v r == 3 \/ v r == 4

type rank = r:usize{is_rank r}


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
let vector_sum #r a = repeati (r -! sz 1)
     (fun i x -> assert (v i < v r - 1); poly_add x (a.[i +! sz 1])) a.[sz 0]

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

