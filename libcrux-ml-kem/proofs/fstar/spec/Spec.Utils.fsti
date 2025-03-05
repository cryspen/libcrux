module Spec.Utils
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open FStar.Mul
open Core

(** Utils *)
let map_slice #a #b
  (f:a -> b)
  (s: t_Slice a)
  = createi (length s) (fun i -> f (Seq.index s (v i)))

let map_array #a #b #len
  (f:a -> b)
  (s: t_Array a len)
  = createi (length s) (fun i -> f (Seq.index s (v i)))

let map2 #a #b #c #len
  (f:a -> b -> c)
  (x: t_Array a len) (y: t_Array b len)
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

val lemma_createi_index #a len f i :
  Lemma (Seq.index (createi #a len f) i == f (sz i))
        [SMTPat (Seq.index (createi #a len f) i)]

val lemma_create_index #a len c i:
  Lemma (Seq.index (create #a len c) i == c)
        [SMTPat (Seq.index (create #a len c) i)]

val lemma_bitand_properties #t (x:int_t t) :
  Lemma ((x &. ones) == x /\ (x &. mk_int #t 0) == mk_int #t 0 /\ (ones #t &. x) == x /\ (mk_int #t 0 &. x) == mk_int #t 0)

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

val v_G (input: t_Slice u8) : t_Array u8 (sz 64)
val v_H (input: t_Slice u8) : t_Array u8 (sz 32)
val v_PRF (v_LEN: usize{v v_LEN < pow2 32}) (input: t_Slice u8) : t_Array u8 v_LEN

val v_PRFxN (r:usize{v r == 2 \/ v r == 3 \/ v r == 4}) (v_LEN: usize{v v_LEN < pow2 32})
  (input: t_Array (t_Array u8 (sz 33)) r) : t_Array (t_Array u8 v_LEN) r

val v_J (input: t_Slice u8) : t_Array u8 (sz 32)

val v_XOF (v_LEN: usize{v v_LEN < pow2 32}) (input: t_Slice u8) : t_Array u8 v_LEN

val update_at_range_lemma #n
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

#push-options "--z3rlimit 200"
val lemma_mul_intb (b1 b2: nat) (n1 n2: int) 
    : Lemma (requires (is_intb b1 n1 /\ is_intb b2 n2))
      (ensures (is_intb (b1 * b2) (n1 * n2)))
#pop-options

#push-options "--z3rlimit 200"
val lemma_mul_i16b (b1 b2: nat) (n1 n2: i16) 
    : Lemma (requires (is_i16b b1 n1 /\ is_i16b b2 n2 /\ b1 * b2 < pow2 31))
      (ensures (range (v n1 * v n2) i32_inttype /\ 
                is_i32b (b1 * b2) ((cast n1 <: i32) *! (cast n2 <: i32)) /\
                v ((cast n1 <: i32) *! (cast n2 <: i32)) == v n1 * v n2))
#pop-options

#push-options "--z3rlimit 200"
val lemma_mul_i32b (b1 b2: nat) (n1 n2: i32) 
    : Lemma (requires (is_i32b b1 n1 /\ is_i32b b2 n2 /\ b1 * b2 < pow2 63))
      (ensures (range (v n1 * v n2) i64_inttype /\ 
                is_i64b (b1 * b2) ((cast n1 <: i64) *! (cast n2 <: i64)) /\
                v ((cast n1 <: i64) *! (cast n2 <: i64)) == v n1 * v n2))
#pop-options

val lemma_add_i16b (b1 b2:nat) (n1 n2:i16) :
  Lemma (requires (is_i16b b1 n1 /\ is_i16b b2 n2 /\ b1 + b2 < pow2 15))
        (ensures (range (v n1 + v n2) i16_inttype /\
                  is_i16b (b1 + b2) (n1 +! n2)))

val lemma_range_at_percent (v:int) (p:int{p>0/\ p%2=0 /\ v < p/2 /\ v >= -p / 2}):
  Lemma (v @% p == v)

val lemma_sub_i16b (b1 b2:nat) (n1 n2:i16) :
  Lemma (requires (is_i16b b1 n1 /\ is_i16b b2 n2 /\ b1 + b2 < pow2 15))
        (ensures (range (v n1 - v n2) i16_inttype /\
                  is_i16b (b1 + b2) (n1 -. n2) /\
                  v (n1 -. n2) == v n1 - v n2))

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

val lemma_at_percent_mod (v:int) (p:int{p>0/\ p%2=0}):
  Lemma ((v @% p) % p == v % p)

val lemma_div_at_percent (v:int) (p:int{p>0/\ p%2=0 /\ (v/p) < p/2 /\ (v/p) >= -p / 2}):
  Lemma ((v / p) @% p == v / p)

val lemma_mont_red_i32 (x:i32): Lemma
  (requires (is_i32b (3328 * pow2 16) x))
  (ensures (
          let result:i16 = mont_red_i32 x in
          is_i16b (3328 + 1665) result /\
          (is_i32b (3328 * pow2 15) x ==> is_i16b 3328 result) /\
          v result % 3329 == (v x * 169) % 3329))

val lemma_mont_mul_red_i16_int (x y:i16): Lemma
  (requires (is_intb (3326 * pow2 15) (v x * v y)))
  (ensures (
          let result:i16 = mont_mul_red_i16 x y in
          is_i16b 3328 result /\
          v result % 3329 == (v x * v y * 169) % 3329))

val lemma_mont_mul_red_i16 (x y:i16): Lemma
  (requires (is_i16b 1664 y \/ is_intb (3326 * pow2 15) (v x * v y)))
  (ensures (
          let result:i16 = mont_mul_red_i16 x y in
          is_i16b 3328 result /\
          v result % 3329 == (v x * v y * 169) % 3329))
          [SMTPat (mont_mul_red_i16 x y)]
 
let barrett_red (x:i16) = 
  let t1 = cast (((cast x <: i32) *. (cast (mk_i16 20159) <: i32)) >>! (mk_i32 16)) <: i16 in
  let t2 = t1 +. (mk_i16 512) in
  let q = t2 >>! (mk_i32 10) in
  let qm = q *. (mk_i16 3329) in
  x -. qm

val lemma_barrett_red (x:i16) : Lemma
   (requires (is_i16b 28296 x))
   (ensures (let result = barrett_red x in
             is_i16b 3328 result /\
             v result % 3329 == v x % 3329)) 
   [SMTPat (barrett_red x)]

let cond_sub (x:i16) =
  let xm = x -. (mk_i16 3329) in
  let mask = xm >>! (mk_i32 15) in
  let mm = mask &. (mk_i16 3329) in
  xm +. mm

val lemma_cond_sub x:
  Lemma (let r = cond_sub x in
         if x >=. (mk_i16 3329) then r == x -! (mk_i16 3329) else r == x)
        [SMTPat (cond_sub x)]

val lemma_shift_right_15_i16 (x:i16):
  Lemma (if v x >= 0 then (x >>! (mk_i32 15)) == mk_i16 0 else (x >>! (mk_i32 15)) == (mk_i16 (-1)))

let ntt_spec #len (vec_in: t_Array i16 len) (zeta: int) (i: nat{i < v len}) (j: nat{j < v len}) 
                  (vec_out: t_Array i16 len) : Type0 =
  ((v (Seq.index vec_out i) % 3329) ==
   ((v (Seq.index vec_in i) + (v (Seq.index vec_in j) * zeta * 169)) % 3329)) /\
  ((v (Seq.index vec_out j) % 3329) ==
   ((v (Seq.index vec_in i) - (v (Seq.index vec_in j) * zeta * 169)) % 3329))

let inv_ntt_spec #len (vec_in: t_Array i16 len) (zeta: int) (i: nat{i < v len}) (j: nat{j < v len}) 
                 (vec_out: t_Array i16 len) : Type0 =
  ((v (Seq.index vec_out i) % 3329) ==
   ((v (Seq.index vec_in j) + v (Seq.index vec_in i)) % 3329)) /\
  ((v (Seq.index vec_out j) % 3329) ==
   (((v (Seq.index vec_in j) - v (Seq.index vec_in i)) * zeta * 169) % 3329))

(* Wrap-around modulo: wraps into ]-p/2; p/2] *)
let mod_q (v:int) (p:int{p>0/\ p%2=0}) : Tot int =
  let m = v % p in if m > p/2 then m - p else m
