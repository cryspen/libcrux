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

let repeati = Lib.LoopCombinators.repeati
  
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

    

