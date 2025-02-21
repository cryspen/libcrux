module Spec.Utils
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open FStar.Mul
open Core

(** Utils *)
let map_slice #a #b
  (f:(x:a -> b))
  (s: t_Slice a): t_Slice b
  = createi (length s) (fun i -> f (Seq.index s (v i)))

let map_array #a #b #len
  (f:(x:a -> b))
  (s: t_Array a len): t_Array b len
  = createi (length s) (fun i -> f (Seq.index s (v i)))

let map2 #a #b #c #len
  (f:a -> b -> c)
  (x: t_Array a len) (y: t_Array b len): t_Array c len
  = createi (length x) (fun i -> f (Seq.index x (v i)) (Seq.index y (v i)))

let create len c = createi len (fun i -> c)

let repeati #acc (l:usize) (f:(i:usize{v i < v l}) -> acc -> acc) acc0 : acc = Lib.LoopCombinators.repeati (v l) (fun i acc -> f (sz i) acc) acc0

let createL len l = Rust_primitives.Hax.array_of_list len l 

let create16 v15 v14 v13 v12 v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 =
  let l = [v15; v14; v13; v12; v11; v10; v9; v8; v7; v6; v5; v4; v3; v2; v1; v0] in
  assert_norm (List.Tot.length l == 16);
  createL 16 l


val lemma_createL_index #a len l i :
  Lemma (Seq.index (createL #a len l) i == List.Tot.index l i)
        [SMTPat (Seq.index (createL #a len l) i)]
let lemma_createL_index #a len l i = ()

val lemma_create16_index #a v15 v14 v13 v12 v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 i :
  Lemma (Seq.index (create16 #a v15 v14 v13 v12 v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0) i ==
        (if i = 0 then v15 else
         if i = 1 then v14 else
         if i = 2 then v13 else
         if i = 3 then v12 else
         if i = 4 then v11 else
         if i = 5 then v10 else
         if i = 6 then v9 else
         if i = 7 then v8 else
         if i = 8 then v7 else
         if i = 9 then v6 else
         if i = 10 then v5 else
         if i = 11 then v4 else
         if i = 12 then v3 else
         if i = 13 then v2 else
         if i = 14 then v1 else
         if i = 15 then v0))
        [SMTPat (Seq.index (create16 #a v15 v14 v13 v12 v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0) i)]
let lemma_create16_index #a v15 v14 v13 v12 v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 i =
  let l = [v15; v14; v13; v12; v11; v10; v9; v8; v7; v6; v5; v4; v3; v2; v1; v0] in
  assert_norm (List.Tot.index l 0 == v15);
  assert_norm (List.Tot.index l 1 == v14);
  assert_norm (List.Tot.index l 2 == v13);
  assert_norm (List.Tot.index l 3 == v12);
  assert_norm (List.Tot.index l 4 == v11);
  assert_norm (List.Tot.index l 5 == v10);
  assert_norm (List.Tot.index l 6 == v9);
  assert_norm (List.Tot.index l 7 == v8);
  assert_norm (List.Tot.index l 8 == v7);
  assert_norm (List.Tot.index l 9 == v6);
  assert_norm (List.Tot.index l 10 == v5);
  assert_norm (List.Tot.index l 11 == v4);
  assert_norm (List.Tot.index l 12 == v3);
  assert_norm (List.Tot.index l 13 == v2);
  assert_norm (List.Tot.index l 14 == v1);
  assert_norm (List.Tot.index l 15 == v0)


val lemma_createi_index #a len f i :
  Lemma (Seq.index (createi #a len f) i == f (sz i))
        [SMTPat (Seq.index (createi #a len f) i)]
let lemma_createi_index #a len f i = ()

val lemma_create_index #a len c i:
  Lemma (Seq.index (create #a len c) i == c)
        [SMTPat (Seq.index (create #a len c) i)]
let lemma_create_index #a len c i = ()

val lemma_map_index #a #b #len f x i:
  Lemma (Seq.index (map_array #a #b #len f x) i == f (Seq.index x i))
        [SMTPat (Seq.index (map_array #a #b #len f x) i)]
let lemma_map_index #a #b #len f x i = ()

val lemma_map2_index #a #b #c #len f x y i:
  Lemma (Seq.index (map2 #a #b #c #len f x y) i == f (Seq.index x i) (Seq.index y i))
        [SMTPat (Seq.index (map2 #a #b #c #len f x y) i)]
let lemma_map2_index #a #b #c #len f x y i = ()
  
let lemma_bitand_properties #t (x:int_t t) :
  Lemma ((x &. ones) == x /\ (x &. mk_int #t 0) == mk_int #t 0 /\ (ones #t &. x) == x /\ (mk_int #t 0 &. x) == mk_int #t 0) = 
    logand_lemma #t x x

#push-options "--z3rlimit 250"
let flatten #t #n
  (#m: usize {range (v n * v m) usize_inttype})
  (x: t_Array (t_Array t m) n)
  : t_Array t (m *! n)
  = createi (m *! n) (fun i -> Seq.index (Seq.index x (v i / v m)) (v i % v m))
#pop-options

type t_Error = | Error_RejectionSampling : t_Error

type t_Result a b = 
  | Ok: a -> t_Result a b
  | Err: b -> t_Result a b

(** Hash Function *)
open Spec.SHA3

let to_secret_byte (x:u8) : Lib.IntTypes.uint8 = Lib.IntTypes.secret (to_uint8 x)
let from_secret_byte (x:Lib.IntTypes.uint8) : u8 = from_uint8 (Lib.RawIntTypes.u8_to_UInt8 x)

val v_G (input: t_Slice u8) : t_Array u8 (sz 64)
let v_G input = map_slice from_secret_byte (sha3_512 (Seq.length input) (map_slice to_secret_byte input))

val v_H (input: t_Slice u8) : t_Array u8 (sz 32)
let v_H input = map_slice from_secret_byte (sha3_256 (Seq.length input) (map_slice to_secret_byte input)) 

val v_PRF (v_LEN: usize{v v_LEN < pow2 32}) (input: t_Slice u8) : t_Array u8 v_LEN
let v_PRF v_LEN input = map_slice from_secret_byte (
  shake256 (Seq.length input) (map_slice to_secret_byte input) (v v_LEN))

assume val v_PRFxN (r:usize{v r == 2 \/ v r == 3 \/ v r == 4}) (v_LEN: usize{v v_LEN < pow2 32})
  (input: t_Array (t_Array u8 (sz 33)) r) : t_Array (t_Array u8 v_LEN) r

let v_J (input: t_Slice u8) : t_Array u8 (sz 32) = v_PRF (sz 32) input

val v_XOF (v_LEN: usize{v v_LEN < pow2 32}) (input: t_Slice u8) : t_Array u8 v_LEN
let v_XOF v_LEN input = map_slice from_secret_byte (
  shake128 (Seq.length input) (map_slice to_secret_byte input) (v v_LEN))

let update_at_range_lemma #n
  (s: t_Slice 't)
  (i: Core.Ops.Range.t_Range (int_t n) {(Core.Ops.Range.impl_index_range_slice 't n).f_index_pre s i}) 
  (x: t_Slice 't)
  : Lemma
    (requires (Seq.length x == v i.f_end - v i.f_start))
    (ensures (
      let s' = Rust_primitives.Hax.Monomorphized_update_at.update_at_range s i x in
      let len = v i.f_start in
      forall (i: nat). i < len ==> Seq.index s i == Seq.index s' i
    ))
    [SMTPat (Rust_primitives.Hax.Monomorphized_update_at.update_at_range s i x)]
  = let s' = Rust_primitives.Hax.Monomorphized_update_at.update_at_range s i x in
    let len = v i.f_start in
    introduce forall (i:nat {i < len}). Seq.index s i == Seq.index s' i
    with (assert ( Seq.index (Seq.slice s  0 len) i == Seq.index s  i 
                 /\ Seq.index (Seq.slice s' 0 len) i == Seq.index s' i ))  


/// Bounded integers

let is_intb (l:nat) (x:int) = (x <= l) && (x >= -l)
let is_i16b (l:nat) (x:i16) = is_intb l (v x)
let is_i16b_array (l:nat) (x:t_Slice i16) = forall i. i < Seq.length x ==> is_i16b l (Seq.index x i)
let is_i16b_vector (l:nat) (r:usize) (x:t_Array (t_Array i16 (sz 256)) r) = forall i. i < v r ==> is_i16b_array l (Seq.index x i)
let is_i16b_matrix (l:nat) (r:usize) (x:t_Array (t_Array (t_Array i16 (sz 256)) r) r) = forall i. i < v r ==> is_i16b_vector l r (Seq.index x i)

[@ "opaque_to_smt"]
let is_i16b_array_opaque (l:nat) (x:t_Slice i16) = is_i16b_array l x

let is_i32b (l:nat) (x:i32) = is_intb l (v x)
let is_i32b_array (l:nat) (x:t_Slice i32) = forall i. i < Seq.length x ==> is_i32b l (Seq.index x i)

let is_i64b (l:nat) (x:i64) = is_intb l (v x)

let nat_div_ceil (x:nat) (y:pos) : nat = if (x % y = 0) then x/y else (x/y)+1

val lemma_intb_le b b'
  : Lemma (requires (b <= b'))
          (ensures (forall n. is_intb b n ==> is_intb b' n))
let lemma_intb_le b b' = ()          

#push-options "--z3rlimit 200"
val lemma_mul_intb (b1 b2: nat) (n1 n2: int) 
    : Lemma (requires (is_intb b1 n1 /\ is_intb b2 n2))
      (ensures (is_intb (b1 * b2) (n1 * n2)))
let lemma_mul_intb (b1 b2: nat) (n1 n2: int) =
  if n1 = 0 || n2 = 0
  then ()
  else 
    let open FStar.Math.Lemmas in
    lemma_abs_bound n1 b1;
    lemma_abs_bound n2 b2;
    lemma_abs_mul n1 n2;
    lemma_mult_le_left (abs n1) (abs n2) b2;
    lemma_mult_le_right b2 (abs n1) b1;
    lemma_abs_bound (n1 * n2) (b1 * b2)
#pop-options

#push-options "--z3rlimit 200"
val lemma_mul_i16b (b1 b2: nat) (n1 n2: i16) 
    : Lemma (requires (is_i16b b1 n1 /\ is_i16b b2 n2 /\ b1 * b2 < pow2 31))
      (ensures (range (v n1 * v n2) i32_inttype /\ 
                is_i32b (b1 * b2) ((cast n1 <: i32) *! (cast n2 <: i32)) /\
                v ((cast n1 <: i32) *! (cast n2 <: i32)) == v n1 * v n2))
      
let lemma_mul_i16b (b1 b2: nat) (n1 n2: i16) =
  if v n1 = 0 || v n2 = 0
  then ()
  else 
    let open FStar.Math.Lemmas in
    lemma_abs_bound (v n1) b1;
    lemma_abs_bound (v n2) b2;
    lemma_abs_mul (v n1) (v n2);
    lemma_mult_le_left (abs (v n1)) (abs (v n2)) b2;
    lemma_mult_le_right b2 (abs (v n1)) b1;
    lemma_abs_bound (v n1 * v n2) (b1 * b2)
#pop-options

#push-options "--z3rlimit 200"
val lemma_mul_i32b (b1 b2: nat) (n1 n2: i32) 
    : Lemma (requires (is_i32b b1 n1 /\ is_i32b b2 n2 /\ b1 * b2 < pow2 63))
      (ensures (range (v n1 * v n2) i64_inttype /\ 
                is_i64b (b1 * b2) ((cast n1 <: i64) *! (cast n2 <: i64)) /\
                v ((cast n1 <: i64) *! (cast n2 <: i64)) == v n1 * v n2))
      
let lemma_mul_i32b (b1 b2: nat) (n1 n2: i32) =
  if v n1 = 0 || v n2 = 0
  then ()
  else 
    let open FStar.Math.Lemmas in
    lemma_abs_bound (v n1) b1;
    lemma_abs_bound (v n2) b2;
    lemma_abs_mul (v n1) (v n2);
    lemma_mult_le_left (abs (v n1)) (abs (v n2)) b2;
    lemma_mult_le_right b2 (abs (v n1)) b1;
    lemma_abs_bound (v n1 * v n2) (b1 * b2)
#pop-options

val lemma_add_i16b (b1 b2:nat) (n1 n2:i16) :
  Lemma (requires (is_i16b b1 n1 /\ is_i16b b2 n2 /\ b1 + b2 < pow2 15))
        (ensures (range (v n1 + v n2) i16_inttype /\
                  is_i16b (b1 + b2) (n1 +! n2)))
let lemma_add_i16b (b1 b2:nat) (n1 n2:i16) = ()

#push-options "--z3rlimit 100 --split_queries always"
let lemma_range_at_percent (v:int) (p:int{p>0/\ p%2=0 /\ v < p/2 /\ v >= -p / 2}):
  Lemma (v @% p == v) =
    let m = v % p in
    if v < 0 then (
      Math.Lemmas.lemma_mod_plus v 1 p;
      assert ((v + p) % p == v % p);
      assert (v + p >= 0);
      assert (v + p < p);
      Math.Lemmas.modulo_lemma (v+p) p;
      assert (m == v + p);
      assert (m >= p/2);
      assert (v @% p == m - p);
      assert (v @% p == v))
    else (
      assert (v >= 0 /\ v < p);
      Math.Lemmas.modulo_lemma v p;
      assert (v % p == v);
      assert (m < p/2);
      assert (v @% p == v)
    )
#pop-options

val lemma_sub_i16b (b1 b2:nat) (n1 n2:i16) :
  Lemma (requires (is_i16b b1 n1 /\ is_i16b b2 n2 /\ b1 + b2 < pow2 15))
        (ensures (range (v n1 - v n2) i16_inttype /\
                  is_i16b (b1 + b2) (n1 -. n2) /\
                  v (n1 -. n2) == v n1 - v n2))
let lemma_sub_i16b (b1 b2:nat) (n1 n2:i16) = ()

let mont_mul_red_i16 (x:i16) (y:i16) : i16=
  let vlow = x *. y in
  let k = vlow *. (neg (mk_i16 3327)) in
  let k_times_modulus = cast (((cast k <: i32) *. (mk_i32 3329)) >>! (mk_i32 16)) <: i16 in
  let vhigh = cast (((cast x <: i32) *. (cast y <: i32)) >>! (mk_i32 16)) <: i16 in
  vhigh -. k_times_modulus

let mont_red_i32 (x:i32) : i16 =
  let vlow = cast x <: i16 in
  let k = vlow *. (neg (mk_i16 3327)) in
  let k_times_modulus = cast (((cast k <: i32) *. (mk_i32 3329)) >>! (mk_i32 16)) <: i16 in
  let vhigh = cast (x >>! (mk_i32 16)) <: i16 in
  vhigh -. k_times_modulus

#push-options "--z3rlimit 100"
let lemma_at_percent_mod (v:int) (p:int{p>0/\ p%2=0}):
  Lemma ((v @% p) % p == v % p) =
  let m = v % p in
  assert (m >= 0 /\ m < p);
  if m >= p/2 then (
    assert ((v @%p) % p == (m - p) %p);
    Math.Lemmas.lemma_mod_plus m (-1) p;
    assert ((v @%p) % p == m %p);
    Math.Lemmas.lemma_mod_mod m v p;
    assert ((v @%p) % p == v % p)
  ) else (
    assert ((v @%p) % p == m%p);
    Math.Lemmas.lemma_mod_mod m v p;
    assert ((v @%p) % p == v % p)
  ) 
#pop-options

let lemma_div_at_percent (v:int) (p:int{p>0/\ p%2=0 /\ (v/p) < p/2 /\ (v/p) >= -p / 2}):
  Lemma ((v / p) @% p == v / p) = 
    lemma_range_at_percent (v/p) p

val lemma_mont_red_i32 (x:i32): Lemma
  (requires (is_i32b (3328 * pow2 16) x))
  (ensures (
          let result:i16 = mont_red_i32 x in
          is_i16b (3328 + 1665) result /\
          (is_i32b (3328 * pow2 15) x ==> is_i16b 3328 result) /\
          v result % 3329 == (v x * 169) % 3329))

let lemma_mont_red_i32 (x:i32) =
  let vlow = cast x <: i16 in
  assert (v vlow == v x @% pow2 16);
  let k = vlow *. (neg (mk_i16 3327)) in
  assert (v k == ((v x @% pow2 16) * (- 3327)) @% pow2 16);
  let k_times_modulus = (cast k <: i32) *. (mk_i32 3329) in
  assert (v k_times_modulus == (v k * 3329));
  let c = cast (k_times_modulus >>! (mk_i32 16)) <: i16 in
  assert (v c == (((v k * 3329) / pow2 16) @% pow2 16));
  lemma_div_at_percent (v k * 3329) (pow2 16);
  assert (v c == (((v k * 3329) / pow2 16)));
  assert (is_i16b 1665 c);
  let vhigh = cast (x >>! (mk_i32 16)) <: i16 in
  lemma_div_at_percent (v x) (pow2 16);
  assert (v vhigh == v x / pow2 16);
  assert (is_i16b 3328 vhigh);
  let result = vhigh -. c in
  lemma_sub_i16b 3328 1665 vhigh c;
  assert (is_i16b (3328 + 1665) result);
  assert (v result = v vhigh - v c);
  assert (is_i16b (3328 + 1665) result);
  assert (is_i32b (3328 * pow2 15) x ==> is_i16b 3328 result);
  calc ( == ) {
      v k_times_modulus % pow2 16;
      ( == ) { assert (v k_times_modulus == v k * 3329) }
      (v k * 3329) % pow2 16;
      ( == ) { assert (v k = ((v x @% pow2 16) * (-3327)) @% pow2 16) }
      ((((v x @% pow2 16) * (-3327)) @% pow2 16) * 3329) % pow2 16;
      ( == ) { Math.Lemmas.lemma_mod_mul_distr_l (((v x @% pow2 16) * (-3327)) @% pow2 16) 3329 (pow2 16) }
      (((((v x @% pow2 16) * (-3327)) @% pow2 16) % pow2 16) * 3329) % pow2 16;
      ( == ) { lemma_at_percent_mod ((v x @% pow2 16) * (-3327)) (pow2 16)}
      ((((v x @% pow2 16) * (-3327)) % pow2 16)  * 3329) % pow2 16;
      ( == ) { Math.Lemmas.lemma_mod_mul_distr_l ((v x @% pow2 16) * (-3327)) 3329 (pow2 16) }
      (((v x @% pow2 16) * (-3327)) * 3329) % pow2 16;
      ( == ) { }
      ((v x @% pow2 16) * (-3327 * 3329)) % pow2 16;
      ( == ) { Math.Lemmas.lemma_mod_mul_distr_r (v x @% pow2 16) (-3327 * 3329) (pow2 16) }
      ((v x @% pow2 16) % pow2 16);
      ( == ) { lemma_at_percent_mod (v x) (pow2 16) }
      (v x) % pow2 16;
    };
    Math.Lemmas.modulo_add (pow2 16) (- (v k_times_modulus)) (v x) (v k_times_modulus);
    assert ((v x - v k_times_modulus) % pow2 16 == 0);
    calc ( == ) {
      v result % 3329;
      ( == ) { }
      (v x / pow2 16 - v k_times_modulus / pow2 16) % 3329;
      ( == ) { Math.Lemmas.lemma_div_exact (v x - v k_times_modulus) (pow2 16) }
      ((v x - v k_times_modulus) / pow2 16) % 3329;
      ( == ) { assert ((pow2 16 * 169) % 3329 == 1) }
      (((v x - v k_times_modulus) / pow2 16) * ((pow2 16 * 169) % 3329)) % 3329;
      ( == ) { Math.Lemmas.lemma_mod_mul_distr_r ((v x - v k_times_modulus) / pow2 16)
        (pow2 16 * 169)
        3329 }
      (((v x - v k_times_modulus) / pow2 16) * pow2 16 * 169) % 3329;
      ( == ) { Math.Lemmas.lemma_div_exact (v x - v k_times_modulus) (pow2 16) }
      ((v x - v k_times_modulus) * 169) % 3329;
      ( == ) { assert (v k_times_modulus == v k * 3329) }
      ((v x * 169) - (v k * 3329 * 169)) % 3329;
      ( == ) { Math.Lemmas.lemma_mod_sub (v x * 169) 3329 (v k * 169) }
      (v x * 169) % 3329;
    }

val lemma_mont_mul_red_i16_int (x y:i16): Lemma
  (requires (is_intb (3326 * pow2 15) (v x * v y)))
  (ensures (
          let result:i16 = mont_mul_red_i16 x y in
          is_i16b 3328 result /\
          v result % 3329 == (v x * v y * 169) % 3329))

#push-options "--z3rlimit 200"

let lemma_mont_mul_red_i16_int (x y:i16) = 
  let vlow = x *. y in
  let prod = v x * v y in
  assert (v vlow == prod @% pow2 16);
  let k = vlow *. (neg (mk_i16 3327)) in
  assert (v k == (((prod) @% pow2 16) * (- 3327)) @% pow2 16);
  let k_times_modulus = (cast k <: i32) *. (mk_i32 3329) in
  assert (v k_times_modulus == (v k * 3329));
  let c = cast (k_times_modulus >>! (mk_i32 16)) <: i16 in
  assert (v c == (((v k * 3329) / pow2 16) @% pow2 16));
  lemma_div_at_percent (v k * 3329) (pow2 16);
  assert (v c == (((v k * 3329) / pow2 16)));
  assert (is_i16b 1665 c);
  let vhigh = cast (((cast x <: i32) *. (cast y <: i32)) >>! (mk_i32 16)) <: i16 in
  assert (v x @% pow2 32 == v x);
  assert (v y @% pow2 32 == v y);
  assert (v ((cast x <: i32) *. (cast y <: i32)) == (v x * v y) @% pow2 32);
  assert (v vhigh == (((prod) @% pow2 32) / pow2 16) @% pow2 16);
  assert_norm (pow2 15 * 3326 < pow2 31);
  lemma_range_at_percent prod (pow2 32);
  assert (v vhigh == (prod / pow2 16) @% pow2 16);
  lemma_div_at_percent prod (pow2 16);
  assert (v vhigh == prod / pow2 16);
  let result = vhigh -. c in
  assert (is_i16b 1663 vhigh);
  lemma_sub_i16b 1663 1665 vhigh c;
  assert (is_i16b 3328 result);
  assert (v result = v vhigh - v c);
  calc ( == ) {
      v k_times_modulus % pow2 16;
      ( == ) { assert (v k_times_modulus == v k * 3329) }
      (v k * 3329) % pow2 16;
      ( == ) { assert (v k = ((prod @% pow2 16) * (-3327)) @% pow2 16) }
      ((((prod @% pow2 16) * (-3327)) @% pow2 16) * 3329) % pow2 16;
      ( == ) { Math.Lemmas.lemma_mod_mul_distr_l (((prod @% pow2 16) * (-3327)) @% pow2 16) 3329 (pow2 16) }
      (((((prod @% pow2 16) * (-3327)) @% pow2 16) % pow2 16) * 3329) % pow2 16;
      ( == ) { lemma_at_percent_mod ((prod @% pow2 16) * (-3327)) (pow2 16)}
      ((((prod @% pow2 16) * (-3327)) % pow2 16)  * 3329) % pow2 16;
      ( == ) { Math.Lemmas.lemma_mod_mul_distr_l ((prod @% pow2 16) * (-3327)) 3329 (pow2 16) }
      (((prod @% pow2 16) * (-3327)) * 3329) % pow2 16;
      ( == ) { }
      ((prod @% pow2 16) * (-3327 * 3329)) % pow2 16;
      ( == ) { Math.Lemmas.lemma_mod_mul_distr_r (prod @% pow2 16) (-3327 * 3329) (pow2 16) }
      ((prod @% pow2 16) % pow2 16);
      ( == ) { lemma_at_percent_mod (prod) (pow2 16) }
      (prod) % pow2 16;
    };
    Math.Lemmas.modulo_add (pow2 16) (- (v k_times_modulus)) ((prod)) (v k_times_modulus);
    assert (((prod) - v k_times_modulus) % pow2 16 == 0);
    calc ( == ) {
      v result % 3329;
      ( == ) { }
      (((prod) / pow2 16) - ((v k * 3329) / pow2 16)) % 3329;
      ( == ) { Math.Lemmas.lemma_div_exact ((prod) - (v k * 3329)) (pow2 16) }
      ((prod - (v k * 3329)) / pow2 16) % 3329;
      ( == ) { assert ((pow2 16 * 169) % 3329 == 1) }
      (((prod - (v k * 3329)) / pow2 16) * ((pow2 16 * 169) % 3329)) % 3329;
      ( == ) { Math.Lemmas.lemma_mod_mul_distr_r (((prod) - (v k * 3329)) / pow2 16)
        (pow2 16 * 169)
        3329 }
      ((((prod) - (v k * 3329)) / pow2 16) * pow2 16 * 169) % 3329;
      ( == ) { Math.Lemmas.lemma_div_exact ((prod) - (v k * 3329)) (pow2 16) }
      (((prod) - (v k * 3329)) * 169) % 3329;
      ( == ) { Math.Lemmas.lemma_mod_sub ((prod) * 169) 3329 (v k * 169)}
      ((prod) * 169) % 3329; 
    }

#pop-options

val lemma_mont_mul_red_i16 (x y:i16): Lemma
  (requires (is_i16b 1664 y \/ is_intb (3326 * pow2 15) (v x * v y)))
  (ensures (
          let result:i16 = mont_mul_red_i16 x y in
          is_i16b 3328 result /\
          v result % 3329 == (v x * v y * 169) % 3329))
          [SMTPat (mont_mul_red_i16 x y)]
let lemma_mont_mul_red_i16 x y =
  if is_i16b 1664 y then (
    lemma_mul_intb (pow2 15) 1664 (v x) (v y);
    assert(is_intb (3326 * pow2 15) (v x * v y));
    lemma_mont_mul_red_i16_int x y) 
  else lemma_mont_mul_red_i16_int x y
 
let barrett_red (x:i16) = 
  let t1 = cast (((cast x <: i32) *. (cast (mk_i16 20159) <: i32)) >>! (mk_i32 16)) <: i16 in
  let t2 = t1 +. (mk_i16 512) in
  let q = t2 >>! (mk_i32 10) in
  let qm = q *. (mk_i16 3329) in
  x -. qm

let lemma_barrett_red (x:i16) : Lemma
   (requires (is_i16b 28296 x))
   (ensures (let result = barrett_red x in
             is_i16b 3328 result /\
             v result % 3329 == v x % 3329)) 
   [SMTPat (barrett_red x)]
   = admit()

let cond_sub (x:i16) =
  let xm = x -. (mk_i16 3329) in
  let mask = xm >>! (mk_i32 15) in
  let mm = mask &. (mk_i16 3329) in
  xm +. mm

let lemma_cond_sub x:
  Lemma (let r = cond_sub x in
         if x >=. (mk_i16 3329) then r == x -! (mk_i16 3329) else r == x)
        [SMTPat (cond_sub x)]
  = admit()


let lemma_shift_right_15_i16 (x:i16):
  Lemma (if v x >= 0 then (x >>! (mk_i32 15)) == mk_i16 0 else (x >>! (mk_i32 15)) == (mk_i16 (-1))) =
  Rust_primitives.Integers.mk_int_v_lemma #i16_inttype (mk_i16 0);
  Rust_primitives.Integers.mk_int_v_lemma #i16_inttype (mk_i16 (-1));
  ()

val ntt_spec #len (vec_in: t_Array i16 len) (zeta: int) (i: nat{i < v len}) (j: nat{j < v len}) 
                  (vec_out: t_Array i16 len) : Type0
let ntt_spec vec_in zeta i j vec_out =
  ((v (Seq.index vec_out i) % 3329) ==
   ((v (Seq.index vec_in i) + (v (Seq.index vec_in j) * zeta * 169)) % 3329)) /\
  ((v (Seq.index vec_out j) % 3329) ==
   ((v (Seq.index vec_in i) - (v (Seq.index vec_in j) * zeta * 169)) % 3329))

val inv_ntt_spec #len (vec_in: t_Array i16 len) (zeta: int) (i: nat{i < v len}) (j: nat{j < v len}) 
                 (vec_out: t_Array i16 len) : Type0
let inv_ntt_spec vec_in zeta i j vec_out =
  ((v (Seq.index vec_out i) % 3329) ==
   ((v (Seq.index vec_in j) + v (Seq.index vec_in i)) % 3329)) /\
  ((v (Seq.index vec_out j) % 3329) ==
   (((v (Seq.index vec_in j) - v (Seq.index vec_in i)) * zeta * 169) % 3329))

