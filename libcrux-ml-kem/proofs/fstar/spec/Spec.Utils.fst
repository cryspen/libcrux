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

let lemma_createi_index #a len f:
  Lemma (forall i. Seq.index (createi #a len f) i == f (sz i)) = admit ()

let lemma_create_index #a len c:
  Lemma (forall i. Seq.index (create #a len c) i == c) = admit ()

let lemma_map_index #a #b #len f x:
  Lemma (forall i. Seq.index (map_array #a #b #len f x) i == f (Seq.index x i)) = admit ()

let lemma_map2_index #a #b #c #len f x y :
  Lemma (forall i. Seq.index (map2 #a #b #c #len f x y) i == f (Seq.index x i) (Seq.index y i)) = admit ()

let lemma_bitand_properties #t (x:int_t t) :
  Lemma ((x &. ones) == x /\ (x &. mk_int #t 0) == mk_int #t 0 /\ (ones #t &. x) == x /\ (mk_int #t 0 &. x) == mk_int #t 0) = admit()

#push-options "--fuel 0 --ifuel 0 --z3rlimit 500"
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

val v_G (input: t_Slice u8) : t_Array u8 (sz 64)
let v_G input = map_slice Lib.RawIntTypes.u8_to_UInt8 (sha3_512 (Seq.length input) (map_slice Lib.IntTypes.secret input))

val v_H (input: t_Slice u8) : t_Array u8 (sz 32)
let v_H input = map_slice Lib.RawIntTypes.u8_to_UInt8 (sha3_256 (Seq.length input) (map_slice Lib.IntTypes.secret input)) 

val v_PRF (v_LEN: usize{v v_LEN < pow2 32}) (input: t_Slice u8) : t_Array u8 v_LEN
let v_PRF v_LEN input = map_slice Lib.RawIntTypes.u8_to_UInt8 (
  shake256 (Seq.length input) (map_slice Lib.IntTypes.secret input) (v v_LEN))

let v_J (input: t_Slice u8) : t_Array u8 (sz 32) = v_PRF (sz 32) input

val v_XOF (v_LEN: usize{v v_LEN < pow2 32}) (input: t_Slice u8) : t_Array u8 v_LEN
let v_XOF v_LEN input = map_slice Lib.RawIntTypes.u8_to_UInt8 (
  shake128 (Seq.length input) (map_slice Lib.IntTypes.secret input) (v v_LEN))

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

let is_i16b (l:nat) (x:i16) = (v x <= l) && (v x >= -l)
let is_i16b_array (l:nat) (x:t_Slice i16) = forall i. i < Seq.length x ==> is_i16b l (Seq.index x i)
let is_i16b_vector (l:nat) (r:usize) (x:t_Array (t_Array i16 (sz 256)) r) = forall i. i < v r ==> is_i16b_array l (Seq.index x i)
let is_i16b_matrix (l:nat) (r:usize) (x:t_Array (t_Array (t_Array i16 (sz 256)) r) r) = forall i. i < v r ==> is_i16b_vector l r (Seq.index x i)

let is_i32b (l:nat) (x:i32) = (v x <= l) && (v x >= -l)
let is_i32b_array (l:nat) (x:t_Slice i32) = forall i. i < Seq.length x ==> is_i32b l (Seq.index x i)

let nat_div_ceil (x:nat) (y:pos) : nat = if (x % y = 0) then x/y else (x/y)+1

val lemma_mul_i16b (b1 b2: nat) (n1 n2: i16) 
    : Lemma (requires (is_i16b b1 n1 /\ is_i16b b2 n2 /\ b1 * b2 < pow2 31))
      (ensures (range (v n1 * v n2) i32_inttype /\ is_i32b (b1 * b2) ((cast n1 <: i32) *! (cast n2 <: i32))))
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

val lemma_add_i16b (b1 b2:nat) (n1 n2:i16) :
  Lemma (requires (is_i16b b1 n1 /\ is_i16b b2 n2 /\ b1 + b2 < pow2 15))
        (ensures (range (v n1 + v n2) i16_inttype /\
                  is_i16b (b1 + b2) (n1 +! n2)))
let lemma_add_i16b (b1 b2:nat) (n1 n2:i16) = ()

let mont_mul_red_i16 (x:i16) (y:i16) : i16=
  let vlow = x *. y in
  let k = vlow *. (neg 3327s) in
  let k_times_modulus = cast (((cast k <: i32) *. 3329l) >>! 16l) <: i16 in
  let vhigh = cast (((cast x <: i32) *. (cast y <: i32)) >>! 16l) <: i16 in
  vhigh -. k_times_modulus

let mont_red_i32 (x:i32) : i16 =
  let vlow = cast x <: i16 in
  let k = vlow *. (neg 3327s) in
  let k_times_modulus = cast (((cast k <: i32) *. 3329l) >>! 16l) <: i16 in
  let vhigh = cast (x >>! 16l) <: i16 in
  vhigh -. k_times_modulus

#push-options "--z3rlimit 900 --split_queries always"
val lemma_mont_red_i32 (x:i32): Lemma
  (requires (Spec.Utils.is_i32b (3328 * pow2 16) x))
  (ensures (
          let result:i16 = mont_red_i32 x in
          Spec.Utils.is_i16b (3328 + 1665) result /\
          (Spec.Utils.is_i32b (3328 * 3328) x ==> Spec.Utils.is_i16b 3328 result) /\
          v result % 3329 == (v x * 169) % 3329))
let lemma_mont_red_i32 (x:i32) =
  let vlow = cast x <: i16 in
  assert (v vlow == v x @% pow2 16);
  let k = vlow *. (neg 3327s) in
  assert (v k == ((v x @% pow2 16) * (- 3327)) @% pow2 16);
  let k_times_modulus = (cast k <: i32) *. 3329l in
  assert (v k_times_modulus == (v k * 3329));
  let c = cast (k_times_modulus >>! 16l) <: i16 in
  assert (v c == (((v k * 3329) / pow2 16) @% pow2 16));
  assert (v c == (((v k * 3329) / pow2 16)));
  assert (is_i16b 1665 c);
  let vhigh = cast (x >>! 16l) <: i16 in
  assert (v vhigh == v x / pow2 16);
  assert (is_i16b 3328 vhigh);
  assert (Spec.Utils.is_i32b (3328 * 3328) x ==> Spec.Utils.is_i16b 169 vhigh);
  let result = vhigh -. c in
  assert (is_i16b (3328 + 1665) result);
  assert (Spec.Utils.is_i32b (3328 * 3328) x ==> Spec.Utils.is_i16b 3328 result);
  calc ( == ) {
      v k_times_modulus % pow2 16;
      ( == ) { assert (v k_times_modulus == v k * 3329) }
      (v k * 3329) % pow2 16;
      ( == ) { assert (v k = ((v x @% pow2 16) * (-3327)) @% pow2 16) }
      ((((v x @% pow2 16) * (-3327)) @% pow2 16) * 3329) % pow2 16;
      ( == ) { Math.Lemmas.lemma_mod_mul_distr_l ((v x @% pow2 16) * (-3327)) 3329 (pow2 16) }
      ((((v x @% pow2 16) * (-3327)) * 3329) % pow2 16);
      ( == ) { Math.Lemmas.lemma_mod_mul_distr_r (v x @% pow2 16) (-3327 * 3329) (pow2 16) }
      ((v x @% pow2 16) % pow2 16);
      ( == ) { Math.Lemmas.lemma_mod_sub (v x) (pow2 16) 1 }
      (v x) % pow2 16;
    };
    Math.Lemmas.modulo_add (pow2 16) (- (v k_times_modulus)) (v x) (v k_times_modulus);
    assert ((v x - v k_times_modulus) % pow2 16 == 0);
    calc ( == ) {
      v result % 3329;
      ( == ) { assert (v result == v vhigh - v c) }
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
      ( == ) { assert (v k_times_modulus == (v k @% pow2 16) * 3329) }
      ((v x * 169) - ((v k @% pow2 16) * 3329 * 169)) % 3329;
      ( == ) { Math.Lemmas.lemma_mod_sub (v x * 169) 3329 ((v k @% pow2 16) * 169) }
      (v x * 169) % 3329;
    }
#pop-options

#push-options "--z3rlimit 1200 --split_queries always --z3refresh"
val lemma_mont_mul_red_i16 (x y:i16): Lemma
  (requires (Spec.Utils.is_i16b 3328 y))
  (ensures (
          let result:i16 = mont_mul_red_i16 x y in
          Spec.Utils.is_i16b (3328 + 1665) result /\
          v result % 3329 == (v x * v y * 169) % 3329))
let lemma_mont_mul_red_i16 (x y:i16) =
  let vlow = x *. y in
  assert (v vlow == (v x * v y) @% pow2 16);
  let k = vlow *. (neg 3327s) in
  assert (v k == (((v x * v y) @% pow2 16) * (- 3327)) @% pow2 16);
  let k_times_modulus = (cast k <: i32) *. 3329l in
  assert (v k_times_modulus == (v k * 3329));
  let c = cast (k_times_modulus >>! 16l) <: i16 in
  assert (v c == (((v k * 3329) / pow2 16) @% pow2 16));
  assert (v c == (((v k * 3329) / pow2 16)));
  assert (is_i16b 1665 c);
  let vhigh = cast (((cast x <: i32) *. (cast y <: i32)) >>! 16l) <: i16 in
  lemma_mul_i16b (pow2 15) (pow2 15) x y;
  assert (is_i32b (pow2 30) ((cast x <: i32) *. (cast y <: i32)));
  assert (v x * v y <= pow2 30 /\ v x * v y >= - pow2 30);
  assert (v x * v y < pow2 31 /\ v x * v y > - pow2 31);
  assert (v vhigh == (((v x * v y) @% pow2 32) / pow2 16) @% pow2 16);
  assert (v vhigh == (v x * v y) / pow2 16);
  assert (is_i16b 3328 vhigh);

  let result = vhigh -. c in
  assert (is_i16b (3328 + 1665) result);
  assert (Spec.Utils.is_i32b (3328 * 3328) x ==> Spec.Utils.is_i16b 3328 result);
  calc ( == ) {
      v k_times_modulus % pow2 16;
      ( == ) { assert (v k_times_modulus == v k * 3329) }
      (v k * 3329) % pow2 16;
      ( == ) { assert (v k = (((v x * v y) @% pow2 16) * (-3327)) @% pow2 16) }
      (((((v x * v y)  @% pow2 16) * (-3327)) @% pow2 16) * 3329) % pow2 16;
      ( == ) { Math.Lemmas.lemma_mod_mul_distr_l (((v x * v y) @% pow2 16) * (-3327)) 3329 (pow2 16) }
      (((((v x * v y) @% pow2 16) * (-3327)) * 3329) % pow2 16);
      ( == ) { Math.Lemmas.lemma_mod_mul_distr_r ((v x * v y) @% pow2 16) (-3327 * 3329) (pow2 16) }
      (((v x * v y) @% pow2 16) % pow2 16);
      ( == ) { Math.Lemmas.lemma_mod_sub ((v x * v y)) (pow2 16) 1 }
      ((v x * v y)) % pow2 16;
    };
    Math.Lemmas.modulo_add (pow2 16) (- (v k_times_modulus)) ((v x * v y)) (v k_times_modulus);
    assert (((v x * v y) - v k_times_modulus) % pow2 16 == 0);
    calc ( == ) {
      v result % 3329;
      ( == ) { assert (v result == v vhigh - v c) }
      ((v x * v y) / pow2 16 - v k_times_modulus / pow2 16) % 3329;
      ( == ) { Math.Lemmas.lemma_div_exact ((v x * v y) - v k_times_modulus) (pow2 16) }
      (((v x * v y) - v k_times_modulus) / pow2 16) % 3329;
      ( == ) { assert ((pow2 16 * 169) % 3329 == 1) }
      ((((v x * v y) - v k_times_modulus) / pow2 16) * ((pow2 16 * 169) % 3329)) % 3329;
      ( == ) { Math.Lemmas.lemma_mod_mul_distr_r (((v x * v y) - v k_times_modulus) / pow2 16)
        (pow2 16 * 169)
        3329 }
      ((((v x * v y) - v k_times_modulus) / pow2 16) * pow2 16 * 169) % 3329;
      ( == ) { Math.Lemmas.lemma_div_exact ((v x * v y) - v k_times_modulus) (pow2 16) }
      (((v x * v y) - v k_times_modulus) * 169) % 3329;
      ( == ) { assert (v k_times_modulus == (v k @% pow2 16) * 3329) }
      (((v x * v y) * 169) - ((v k @% pow2 16) * 3329 * 169)) % 3329;
      ( == ) { Math.Lemmas.lemma_mod_sub ((v x * v y) * 169) 3329 ((v k @% pow2 16) * 169) }
      ((v x * v y) * 169) % 3329;
    }
#pop-options
