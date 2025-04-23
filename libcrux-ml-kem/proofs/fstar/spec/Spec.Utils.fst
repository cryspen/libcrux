module Spec.Utils
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open FStar.Mul
open Core

let lemma_createL_index #a len l i = ()

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

let lemma_createi_index #a len f i = ()

let lemma_create_index #a len c i = ()


let lemma_bitand_properties #t (x:int_t t) =
    logand_lemma #t x x

(** Hash Function *)
open Spec.SHA3

let to_secret_byte (x:u8) : Lib.IntTypes.uint8 = Lib.IntTypes.secret (to_uint8 x)
let from_secret_byte (x:Lib.IntTypes.uint8) : u8 = from_uint8 (Lib.RawIntTypes.u8_to_UInt8 x)

let v_G input = map_slice from_secret_byte (sha3_512 (Seq.length input) (map_slice to_secret_byte input))

let v_H input = map_slice from_secret_byte (sha3_256 (Seq.length input) (map_slice to_secret_byte input)) 

let v_PRF v_LEN input = map_slice from_secret_byte (
  shake256 (Seq.length input) (map_slice to_secret_byte input) (v v_LEN))

let v_PRFxN r v_LEN input = admit()

let v_J (input: t_Slice u8) : t_Array u8 (sz 32) = v_PRF (sz 32) input

let v_XOF v_LEN input = map_slice from_secret_byte (
  shake128 (Seq.length input) (map_slice to_secret_byte input) (v v_LEN))

let update_at_range_lemma #n
  (s: t_Slice 't)
  (i: Core.Ops.Range.t_Range (int_t n) {(Core.Ops.Range.impl_index_range_slice 't n).f_index_pre s i}) 
  (x: t_Slice 't)
  = let s' = Rust_primitives.Hax.Monomorphized_update_at.update_at_range s i x in
    let len = v i.f_start in
    introduce forall (i:nat {i < len}). Seq.index s i == Seq.index s' i
    with (assert ( Seq.index (Seq.slice s  0 len) i == Seq.index s  i 
                 /\ Seq.index (Seq.slice s' 0 len) i == Seq.index s' i ))  


/// Bounded integers

let lemma_intb_le b b' = ()          

#push-options "--z3rlimit 200"
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

let lemma_add_i16b (b1 b2:nat) (n1 n2:i16) = ()

#push-options "--z3rlimit 100 --split_queries always"
let lemma_range_at_percent (v:int) (p:int{p>0/\ p%2=0 /\ v < p/2 /\ v >= -p / 2}) =
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

let lemma_sub_i16b (b1 b2:nat) (n1 n2:i16) = ()

#push-options "--z3rlimit 100"
let lemma_at_percent_mod (v:int) (p:int{p>0/\ p%2=0}) =
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

let lemma_div_at_percent (v:int) (p:int{p>0/\ p%2=0 /\ (v/p) < p/2 /\ (v/p) >= -p / 2}) =
    lemma_range_at_percent (v/p) p

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

let lemma_mont_mul_red_i16 x y =
  if is_i16b 1664 y then (
    lemma_mul_intb (pow2 15) 1664 (v x) (v y);
    assert(is_intb (3326 * pow2 15) (v x * v y));
    lemma_mont_mul_red_i16_int x y) 
  else lemma_mont_mul_red_i16_int x y

let lemma_barrett_red (x:i16) = admit()

let lemma_cond_sub x = admit()

let lemma_shift_right_15_i16 (x:i16) =
  Rust_primitives.Integers.mk_int_v_lemma #i16_inttype (mk_i16 0);
  Rust_primitives.Integers.mk_int_v_lemma #i16_inttype (mk_i16 (-1));
  ()


