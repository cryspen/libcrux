module RwLemmas

open Core
module L = FStar.List.Tot
open FStar.Tactics.V2
open FStar.Tactics.V2.SyntaxHelpers
open FStar.Class.Printable
open FStar.Mul
open FStar.Option

open Tactics.Utils
open Tactics.Pow2

open BitVecEq {}

#push-options "--z3rlimit 40"
let deserialize_10_int (bytes: t_Array u8 (sz 10)) =
  let r0:i16 =
    (((cast (bytes.[ sz 1 ] <: u8) <: i16) &. 3s <: i16) <<! 8l <: i16) |.
    ((cast (bytes.[ sz 0 ] <: u8) <: i16) &. 255s <: i16)
  in
  let r1:i16 =
    (((cast (bytes.[ sz 2 ] <: u8) <: i16) &. 15s <: i16) <<! 6l <: i16) |.
    ((cast (bytes.[ sz 1 ] <: u8) <: i16) >>! 2l <: i16)
  in
  let r2:i16 =
    (((cast (bytes.[ sz 3 ] <: u8) <: i16) &. 63s <: i16) <<! 4l <: i16) |.
    ((cast (bytes.[ sz 2 ] <: u8) <: i16) >>! 4l <: i16)
  in
  let r3:i16 =
    ((cast (bytes.[ sz 4 ] <: u8) <: i16) <<! 2l <: i16) |.
    ((cast (bytes.[ sz 3 ] <: u8) <: i16) >>! 6l <: i16)
  in
  let r4:i16 =
    (((cast (bytes.[ sz 6 ] <: u8) <: i16) &. 3s <: i16) <<! 8l <: i16) |.
    ((cast (bytes.[ sz 5 ] <: u8) <: i16) &. 255s <: i16)
  in
  let r5:i16 =
    (((cast (bytes.[ sz 7 ] <: u8) <: i16) &. 15s <: i16) <<! 6l <: i16) |.
    ((cast (bytes.[ sz 6 ] <: u8) <: i16) >>! 2l <: i16)
  in
  let r6:i16 =
    (((cast (bytes.[ sz 8 ] <: u8) <: i16) &. 63s <: i16) <<! 4l <: i16) |.
    ((cast (bytes.[ sz 7 ] <: u8) <: i16) >>! 4l <: i16)
  in
  let r7:i16 =
    ((cast (bytes.[ sz 9 ] <: u8) <: i16) <<! 2l <: i16) |.
    ((cast (bytes.[ sz 8 ] <: u8) <: i16) >>! 6l <: i16)
  in
  let result:(i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16) =
    r0, r1, r2, r3, r4, r5, r6, r7 <: (i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16)
  in
  result
#pop-options

let deserialize_10_int' (bytes: t_Array u8 (sz 10)): t_Array i16 (sz 8)
    = MkSeq.create8 (deserialize_10_int bytes)

#push-options "--compat_pre_core 0"
#push-options "--z3rlimit 80"
let fff_ (bytes: t_Array u8 (sz 10)) x: unit = 
    let bv1 = bit_vec_of_int_t_array bytes 8 in
    let out = deserialize_10_int' bytes in
    let bv2 = bit_vec_of_int_t_array out 10 in
    assert (forall (i: nat { i < 80 }). bv1 i == bv2 i) by (
      Tactics.GetBit.prove_bit_vector_equality ()
    )
#pop-options

