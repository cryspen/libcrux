module Spec.Utils
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Spec.SHA3
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

let map2 #a #b #c (#len:usize{v len < pow2 32})
  (f:a -> b -> c)
  (x: t_Array a len) (y: t_Array b len): t_Array c len
  = Lib.Sequence.map2 #a #b #c #(v len) f x y

let repeati #acc (l:usize) (f:(i:usize{v i < v l}) -> acc -> acc) acc0 : acc = Lib.LoopCombinators.repeati (v l) (fun i acc -> f (sz i) acc) acc0
  
#push-options "--z3rlimit 500"
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

let lemma_mul_i16b (b1 b2: nat) (n1 n2: i16) 
    : Lemma (requires (is_i16b b1 n1 /\ is_i16b b2 n2 /\ b1 * b2 < pow2 31))
      (ensures (range (v n1 * v n2) i32_inttype /\ is_i32b (b1 * b2) ((cast n1 <: i32) *! (cast n2 <: i32)))) =
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

let lemma_add_i16b (b1 b2:nat) (n1 n2:i16) :
  Lemma (requires (is_i16b b1 n1 /\ is_i16b b2 n2 /\ b1 + b2 < pow2 15))
        (ensures (range (v n1 + v n2) i16_inttype /\
                  is_i16b (b1 + b2) (n1 +! n2)))
  = ()

