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

let is_intb (l:nat) (x:int) = (x <= l) && (x >= -l)
let is_i16b (l:nat) (x:i16) = is_intb l (v x)
let is_i16b_array (l:nat) (x:t_Slice i16) = forall i. i < Seq.length x ==> is_i16b l (Seq.index x i)
let is_i16b_vector (l:nat) (r:usize) (x:t_Array (t_Array i16 (sz 256)) r) = forall i. i < v r ==> is_i16b_array l (Seq.index x i)
let is_i16b_matrix (l:nat) (r:usize) (x:t_Array (t_Array (t_Array i16 (sz 256)) r) r) = forall i. i < v r ==> is_i16b_vector l r (Seq.index x i)

let is_i32b (l:nat) (x:i32) = is_intb l (v x)
let is_i32b_array (l:nat) (x:t_Slice i32) = forall i. i < Seq.length x ==> is_i32b l (Seq.index x i)

let nat_div_ceil (x:nat) (y:pos) : nat = if (x % y = 0) then x/y else (x/y)+1

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


#push-options "--z3rlimit 250"
let lemma_range_at_percent (v:int) (p:int{p>0/\ p%2=0 /\ v < p/2 /\ v >= -p / 2}):
  Lemma (v @% p == v) = ()
#pop-options

val lemma_sub_i16b (b1 b2:nat) (n1 n2:i16) :
  Lemma (requires (is_i16b b1 n1 /\ is_i16b b2 n2 /\ b1 + b2 < pow2 15))
        (ensures (range (v n1 - v n2) i16_inttype /\
                  is_i16b (b1 + b2) (n1 -. n2) /\
                  v (n1 -. n2) == v n1 - v n2))
let lemma_sub_i16b (b1 b2:nat) (n1 n2:i16) = ()

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

#push-options "--z3rlimit 250"
let lemma_at_percent_mod (v:int) (p:int{p>0/\ p%2=0}):
  Lemma ((v @% p) % p == v % p) = ()
#pop-options

let lemma_div_at_percent (v:int) (p:int{p>0/\ p%2=0 /\ (v/p) < p/2 /\ (v/p) >= -p / 2}):
  Lemma ((v / p) @% p == v / p) = 
    lemma_range_at_percent (v/p) p

val lemma_mont_red_i32 (x:i32): Lemma
  (requires (is_i32b (3328 * pow2 16) x))
  (ensures (
          let result:i16 = mont_red_i32 x in
          is_i16b (3328 + 1665) result /\
          (is_i32b (3328 * 3328) x ==> is_i16b 3328 result) /\
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
  lemma_div_at_percent (v k * 3329) (pow2 16);
  assert (v c == (((v k * 3329) / pow2 16)));
  assert (is_i16b 1665 c);
  let vhigh = cast (x >>! 16l) <: i16 in
  lemma_div_at_percent (v x) (pow2 16);
  assert (v vhigh == v x / pow2 16);
  assert (is_i16b 3328 vhigh);
  assert (is_i32b (3328 * 3328) x ==> is_i16b 169 vhigh);
  let result = vhigh -. c in
  lemma_sub_i16b 3328 1665 vhigh c;
  assert (is_i16b (3328 + 1665) result);
  assert (v result = v vhigh - v c);
  assert (is_i16b (3328 + 1665) result);
  assert (is_i32b (3328 * 3328) x ==> is_i16b 3328 result);
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

val lemma_mont_mul_red_i16 (x y:i16): Lemma
  (requires (is_i16b 3328 y))
  (ensures (
          let result:i16 = mont_mul_red_i16 x y in
          is_i16b 3329 result /\
          v result % 3329 == (v x * v y * 169) % 3329))
          [SMTPat (mont_mul_red_i16 x y)]
let lemma_mont_mul_red_i16 (x y:i16) = 
  let vlow = x *. y in
  let prod = v x * v y in
  assert (v vlow == prod @% pow2 16);
  let k = vlow *. (neg 3327s) in
  assert (v k == (((prod) @% pow2 16) * (- 3327)) @% pow2 16);
  let k_times_modulus = (cast k <: i32) *. 3329l in
  assert (v k_times_modulus == (v k * 3329));
  let c = cast (k_times_modulus >>! 16l) <: i16 in
  assert (v c == (((v k * 3329) / pow2 16) @% pow2 16));
  lemma_div_at_percent (v k * 3329) (pow2 16);
  assert (v c == (((v k * 3329) / pow2 16)));
  assert (is_i16b 1665 c);
  let vhigh = cast (((cast x <: i32) *. (cast y <: i32)) >>! 16l) <: i16 in
  lemma_mul_intb (pow2 15) 3328 (v x) (v y);
  assert (v x @% pow2 32 == v x);
  assert (v y @% pow2 32 == v y);
  assert (v ((cast x <: i32) *. (cast y <: i32)) == (v x * v y) @% pow2 32);
  assert (v vhigh == (((prod) @% pow2 32) / pow2 16) @% pow2 16);
  assert_norm (pow2 15 * 3328 < pow2 31);
  lemma_range_at_percent prod (pow2 32);
  assert (v vhigh == (prod / pow2 16) @% pow2 16);
  lemma_div_at_percent prod (pow2 16);
  assert (v vhigh == prod / pow2 16);
  assert (is_i16b 1664 vhigh);
  let result = vhigh -. c in
  lemma_sub_i16b 1664 1665 vhigh c;
  assert (is_i16b 3329 result);
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


let barrett_red (x:i16) = 
  let t1 = cast (((cast x <: i32) *. (cast 20159s <: i32)) >>! 16l) <: i16 in
  let t2 = t1 +. 512s in
  let q = t2 >>! 10l in
  let qm = q *. 3329s in
  x -. qm

let lemma_barrett_red (x:i16) : Lemma
   (requires (Spec.Utils.is_i16b 28296 x))
   (ensures (let result = barrett_red x in
             Spec.Utils.is_i16b 3328 result /\
             v result % 3329 == v x % 3329)) 
   [SMTPat (barrett_red x)]
   = admit()

let cond_sub (x:i16) =
  let xm = x -. 3329s in
  let mask = xm >>! 15l in
  let mm = mask &. 3329s in
  xm +. mm

let lemma_cond_sub x:
  Lemma (let r = cond_sub x in
         if x >=. 3329s then r == x -! 3329s else r == x)
        [SMTPat (cond_sub x)]
  = admit()

