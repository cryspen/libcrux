module Libcrux_ml_kem.Vector.Portable.Serialize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let deserialize_10_int (bytes: t_Slice u8) =
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
  r0, r1, r2, r3, r4, r5, r6, r7 <: (i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16)

let deserialize_11_int (bytes: t_Slice u8) =
  let r0:i16 =
    (((cast (bytes.[ sz 1 ] <: u8) <: i16) &. 7s <: i16) <<! 8l <: i16) |.
    (cast (bytes.[ sz 0 ] <: u8) <: i16)
  in
  let r1:i16 =
    (((cast (bytes.[ sz 2 ] <: u8) <: i16) &. 63s <: i16) <<! 5l <: i16) |.
    ((cast (bytes.[ sz 1 ] <: u8) <: i16) >>! 3l <: i16)
  in
  let r2:i16 =
    ((((cast (bytes.[ sz 4 ] <: u8) <: i16) &. 1s <: i16) <<! 10l <: i16) |.
      ((cast (bytes.[ sz 3 ] <: u8) <: i16) <<! 2l <: i16)
      <:
      i16) |.
    ((cast (bytes.[ sz 2 ] <: u8) <: i16) >>! 6l <: i16)
  in
  let r3:i16 =
    (((cast (bytes.[ sz 5 ] <: u8) <: i16) &. 15s <: i16) <<! 7l <: i16) |.
    ((cast (bytes.[ sz 4 ] <: u8) <: i16) >>! 1l <: i16)
  in
  let r4:i16 =
    (((cast (bytes.[ sz 6 ] <: u8) <: i16) &. 127s <: i16) <<! 4l <: i16) |.
    ((cast (bytes.[ sz 5 ] <: u8) <: i16) >>! 4l <: i16)
  in
  let r5:i16 =
    ((((cast (bytes.[ sz 8 ] <: u8) <: i16) &. 3s <: i16) <<! 9l <: i16) |.
      ((cast (bytes.[ sz 7 ] <: u8) <: i16) <<! 1l <: i16)
      <:
      i16) |.
    ((cast (bytes.[ sz 6 ] <: u8) <: i16) >>! 7l <: i16)
  in
  let r6:i16 =
    (((cast (bytes.[ sz 9 ] <: u8) <: i16) &. 31s <: i16) <<! 6l <: i16) |.
    ((cast (bytes.[ sz 8 ] <: u8) <: i16) >>! 2l <: i16)
  in
  let r7:i16 =
    ((cast (bytes.[ sz 10 ] <: u8) <: i16) <<! 3l <: i16) |.
    ((cast (bytes.[ sz 9 ] <: u8) <: i16) >>! 5l <: i16)
  in
  r0, r1, r2, r3, r4, r5, r6, r7 <: (i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16)

let deserialize_12_int (bytes: t_Slice u8) =
  let byte0:i16 = cast (bytes.[ sz 0 ] <: u8) <: i16 in
  let byte1:i16 = cast (bytes.[ sz 1 ] <: u8) <: i16 in
  let byte2:i16 = cast (bytes.[ sz 2 ] <: u8) <: i16 in
  let r0:i16 = ((byte1 &. 15s <: i16) <<! 8l <: i16) |. (byte0 &. 255s <: i16) in
  let r1:i16 = (byte2 <<! 4l <: i16) |. ((byte1 >>! 4l <: i16) &. 15s <: i16) in
  r0, r1 <: (i16 & i16)

let deserialize_4_int (bytes: t_Slice u8) =
  let v0:i16 = cast ((bytes.[ sz 0 ] <: u8) &. 15uy <: u8) <: i16 in
  let v1:i16 = cast (((bytes.[ sz 0 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i16 in
  let v2:i16 = cast ((bytes.[ sz 1 ] <: u8) &. 15uy <: u8) <: i16 in
  let v3:i16 = cast (((bytes.[ sz 1 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i16 in
  let v4:i16 = cast ((bytes.[ sz 2 ] <: u8) &. 15uy <: u8) <: i16 in
  let v5:i16 = cast (((bytes.[ sz 2 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i16 in
  let v6:i16 = cast ((bytes.[ sz 3 ] <: u8) &. 15uy <: u8) <: i16 in
  let v7:i16 = cast (((bytes.[ sz 3 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i16 in
  v0, v1, v2, v3, v4, v5, v6, v7 <: (i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16)

let deserialize_5_int (bytes: t_Slice u8) =
  let v0:i16 = cast ((bytes.[ sz 0 ] <: u8) &. 31uy <: u8) <: i16 in
  let v1:i16 =
    cast ((((bytes.[ sz 1 ] <: u8) &. 3uy <: u8) <<! 3l <: u8) |.
        ((bytes.[ sz 0 ] <: u8) >>! 5l <: u8)
        <:
        u8)
    <:
    i16
  in
  let v2:i16 = cast (((bytes.[ sz 1 ] <: u8) >>! 2l <: u8) &. 31uy <: u8) <: i16 in
  let v3:i16 =
    cast ((((bytes.[ sz 2 ] <: u8) &. 15uy <: u8) <<! 1l <: u8) |.
        ((bytes.[ sz 1 ] <: u8) >>! 7l <: u8)
        <:
        u8)
    <:
    i16
  in
  let v4:i16 =
    cast ((((bytes.[ sz 3 ] <: u8) &. 1uy <: u8) <<! 4l <: u8) |.
        ((bytes.[ sz 2 ] <: u8) >>! 4l <: u8)
        <:
        u8)
    <:
    i16
  in
  let v5:i16 = cast (((bytes.[ sz 3 ] <: u8) >>! 1l <: u8) &. 31uy <: u8) <: i16 in
  let v6:i16 =
    cast ((((bytes.[ sz 4 ] <: u8) &. 7uy <: u8) <<! 2l <: u8) |.
        ((bytes.[ sz 3 ] <: u8) >>! 6l <: u8)
        <:
        u8)
    <:
    i16
  in
  let v7:i16 = cast ((bytes.[ sz 4 ] <: u8) >>! 3l <: u8) <: i16 in
  v0, v1, v2, v3, v4, v5, v6, v7 <: (i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16)

let serialize_10_int (v: t_Slice i16) =
  let r0:u8 = cast ((v.[ sz 0 ] <: i16) &. 255s <: i16) <: u8 in
  let r1:u8 =
    ((cast ((v.[ sz 1 ] <: i16) &. 63s <: i16) <: u8) <<! 2l <: u8) |.
    (cast (((v.[ sz 0 ] <: i16) >>! 8l <: i16) &. 3s <: i16) <: u8)
  in
  let r2:u8 =
    ((cast ((v.[ sz 2 ] <: i16) &. 15s <: i16) <: u8) <<! 4l <: u8) |.
    (cast (((v.[ sz 1 ] <: i16) >>! 6l <: i16) &. 15s <: i16) <: u8)
  in
  let r3:u8 =
    ((cast ((v.[ sz 3 ] <: i16) &. 3s <: i16) <: u8) <<! 6l <: u8) |.
    (cast (((v.[ sz 2 ] <: i16) >>! 4l <: i16) &. 63s <: i16) <: u8)
  in
  let r4:u8 = cast (((v.[ sz 3 ] <: i16) >>! 2l <: i16) &. 255s <: i16) <: u8 in
  r0, r1, r2, r3, r4 <: (u8 & u8 & u8 & u8 & u8)

let serialize_11_int (v: t_Slice i16) =
  let r0:u8 = cast (v.[ sz 0 ] <: i16) <: u8 in
  let r1:u8 =
    ((cast ((v.[ sz 1 ] <: i16) &. 31s <: i16) <: u8) <<! 3l <: u8) |.
    (cast ((v.[ sz 0 ] <: i16) >>! 8l <: i16) <: u8)
  in
  let r2:u8 =
    ((cast ((v.[ sz 2 ] <: i16) &. 3s <: i16) <: u8) <<! 6l <: u8) |.
    (cast ((v.[ sz 1 ] <: i16) >>! 5l <: i16) <: u8)
  in
  let r3:u8 = cast (((v.[ sz 2 ] <: i16) >>! 2l <: i16) &. 255s <: i16) <: u8 in
  let r4:u8 =
    ((cast ((v.[ sz 3 ] <: i16) &. 127s <: i16) <: u8) <<! 1l <: u8) |.
    (cast ((v.[ sz 2 ] <: i16) >>! 10l <: i16) <: u8)
  in
  let r5:u8 =
    ((cast ((v.[ sz 4 ] <: i16) &. 15s <: i16) <: u8) <<! 4l <: u8) |.
    (cast ((v.[ sz 3 ] <: i16) >>! 7l <: i16) <: u8)
  in
  let r6:u8 =
    ((cast ((v.[ sz 5 ] <: i16) &. 1s <: i16) <: u8) <<! 7l <: u8) |.
    (cast ((v.[ sz 4 ] <: i16) >>! 4l <: i16) <: u8)
  in
  let r7:u8 = cast (((v.[ sz 5 ] <: i16) >>! 1l <: i16) &. 255s <: i16) <: u8 in
  let r8:u8 =
    ((cast ((v.[ sz 6 ] <: i16) &. 63s <: i16) <: u8) <<! 2l <: u8) |.
    (cast ((v.[ sz 5 ] <: i16) >>! 9l <: i16) <: u8)
  in
  let r9:u8 =
    ((cast ((v.[ sz 7 ] <: i16) &. 7s <: i16) <: u8) <<! 5l <: u8) |.
    (cast ((v.[ sz 6 ] <: i16) >>! 6l <: i16) <: u8)
  in
  let r10:u8 = cast ((v.[ sz 7 ] <: i16) >>! 3l <: i16) <: u8 in
  r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10
  <:
  (u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8)

let serialize_12_int (v: t_Slice i16) =
  let r0:u8 = cast ((v.[ sz 0 ] <: i16) &. 255s <: i16) <: u8 in
  let r1:u8 =
    cast (((v.[ sz 0 ] <: i16) >>! 8l <: i16) |. (((v.[ sz 1 ] <: i16) &. 15s <: i16) <<! 4l <: i16)
        <:
        i16)
    <:
    u8
  in
  let r2:u8 = cast (((v.[ sz 1 ] <: i16) >>! 4l <: i16) &. 255s <: i16) <: u8 in
  r0, r1, r2 <: (u8 & u8 & u8)

let serialize_4_int (v: t_Slice i16) =
  let result0:u8 =
    ((cast (v.[ sz 1 ] <: i16) <: u8) <<! 4l <: u8) |. (cast (v.[ sz 0 ] <: i16) <: u8)
  in
  let result1:u8 =
    ((cast (v.[ sz 3 ] <: i16) <: u8) <<! 4l <: u8) |. (cast (v.[ sz 2 ] <: i16) <: u8)
  in
  let result2:u8 =
    ((cast (v.[ sz 5 ] <: i16) <: u8) <<! 4l <: u8) |. (cast (v.[ sz 4 ] <: i16) <: u8)
  in
  let result3:u8 =
    ((cast (v.[ sz 7 ] <: i16) <: u8) <<! 4l <: u8) |. (cast (v.[ sz 6 ] <: i16) <: u8)
  in
  result0, result1, result2, result3 <: (u8 & u8 & u8 & u8)

let serialize_5_int (v: t_Slice i16) =
  let r0:u8 = cast ((v.[ sz 0 ] <: i16) |. ((v.[ sz 1 ] <: i16) <<! 5l <: i16) <: i16) <: u8 in
  let r1:u8 =
    cast ((((v.[ sz 1 ] <: i16) >>! 3l <: i16) |. ((v.[ sz 2 ] <: i16) <<! 2l <: i16) <: i16) |.
        ((v.[ sz 3 ] <: i16) <<! 7l <: i16)
        <:
        i16)
    <:
    u8
  in
  let r2:u8 =
    cast (((v.[ sz 3 ] <: i16) >>! 1l <: i16) |. ((v.[ sz 4 ] <: i16) <<! 4l <: i16) <: i16) <: u8
  in
  let r3:u8 =
    cast ((((v.[ sz 4 ] <: i16) >>! 4l <: i16) |. ((v.[ sz 5 ] <: i16) <<! 1l <: i16) <: i16) |.
        ((v.[ sz 6 ] <: i16) <<! 6l <: i16)
        <:
        i16)
    <:
    u8
  in
  let r4:u8 =
    cast (((v.[ sz 6 ] <: i16) >>! 2l <: i16) |. ((v.[ sz 7 ] <: i16) <<! 3l <: i16) <: i16) <: u8
  in
  r0, r1, r2, r3, r4 <: (u8 & u8 & u8 & u8 & u8)

let deserialize_1_ (v: t_Slice u8) =
  let result0:i16 = cast ((v.[ sz 0 ] <: u8) &. 1uy <: u8) <: i16 in
  let result1:i16 = cast (((v.[ sz 0 ] <: u8) >>! 1l <: u8) &. 1uy <: u8) <: i16 in
  let result2:i16 = cast (((v.[ sz 0 ] <: u8) >>! 2l <: u8) &. 1uy <: u8) <: i16 in
  let result3:i16 = cast (((v.[ sz 0 ] <: u8) >>! 3l <: u8) &. 1uy <: u8) <: i16 in
  let result4:i16 = cast (((v.[ sz 0 ] <: u8) >>! 4l <: u8) &. 1uy <: u8) <: i16 in
  let result5:i16 = cast (((v.[ sz 0 ] <: u8) >>! 5l <: u8) &. 1uy <: u8) <: i16 in
  let result6:i16 = cast (((v.[ sz 0 ] <: u8) >>! 6l <: u8) &. 1uy <: u8) <: i16 in
  let result7:i16 = cast (((v.[ sz 0 ] <: u8) >>! 7l <: u8) &. 1uy <: u8) <: i16 in
  let result8:i16 = cast ((v.[ sz 1 ] <: u8) &. 1uy <: u8) <: i16 in
  let result9:i16 = cast (((v.[ sz 1 ] <: u8) >>! 1l <: u8) &. 1uy <: u8) <: i16 in
  let result10:i16 = cast (((v.[ sz 1 ] <: u8) >>! 2l <: u8) &. 1uy <: u8) <: i16 in
  let result11:i16 = cast (((v.[ sz 1 ] <: u8) >>! 3l <: u8) &. 1uy <: u8) <: i16 in
  let result12:i16 = cast (((v.[ sz 1 ] <: u8) >>! 4l <: u8) &. 1uy <: u8) <: i16 in
  let result13:i16 = cast (((v.[ sz 1 ] <: u8) >>! 5l <: u8) &. 1uy <: u8) <: i16 in
  let result14:i16 = cast (((v.[ sz 1 ] <: u8) >>! 6l <: u8) &. 1uy <: u8) <: i16 in
  let result15:i16 = cast (((v.[ sz 1 ] <: u8) >>! 7l <: u8) &. 1uy <: u8) <: i16 in
  {
    Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
    =
    let list =
      [
        result0; result1; result2; result3; result4; result5; result6; result7; result8; result9;
        result10; result11; result12; result13; result14; result15
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
    Rust_primitives.Hax.array_of_list 16 list
  }
  <:
  Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector

#push-options "--compat_pre_core 2 --z3rlimit 300 --z3refresh"

let deserialize_1_bit_vec_lemma (v: t_Array u8 (sz 2))
   : squash (
     let inputs = bit_vec_of_int_t_array v 8 in
     let outputs = bit_vec_of_int_t_array (deserialize_1_ v).f_elements 1 in
     (forall (i: nat {i < 16}). inputs i == outputs i)
   ) =
  _ by (Tactics.GetBit.prove_bit_vector_equality' ())

#pop-options

#push-options "--z3rlimit 300"

let deserialize_1_lemma inputs =
  deserialize_1_bit_vec_lemma inputs;
  BitVecEq.bit_vec_equal_intro (bit_vec_of_int_t_array (deserialize_1_ inputs).f_elements 1) 
    (BitVecEq.retype (bit_vec_of_int_t_array inputs 8))

#pop-options

let deserialize_1_bounded_lemma inputs =
  admit()

let deserialize_10_ (bytes: t_Slice u8) =
  let v0_7_:(i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16) =
    deserialize_10_int (bytes.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 10 }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let v8_15_:(i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16) =
    deserialize_10_int (bytes.[ { Core.Ops.Range.f_start = sz 10; Core.Ops.Range.f_end = sz 20 }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  {
    Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
    =
    let list =
      [
        v0_7_._1; v0_7_._2; v0_7_._3; v0_7_._4; v0_7_._5; v0_7_._6; v0_7_._7; v0_7_._8; v8_15_._1;
        v8_15_._2; v8_15_._3; v8_15_._4; v8_15_._5; v8_15_._6; v8_15_._7; v8_15_._8
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
    Rust_primitives.Hax.array_of_list 16 list
  }
  <:
  Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector

#push-options "--compat_pre_core 2 --z3rlimit 300 --z3refresh"

let deserialize_10_bit_vec_lemma (v: t_Array u8 (sz 20))
   : squash (
     let inputs = bit_vec_of_int_t_array v 8 in
     let outputs = bit_vec_of_int_t_array (deserialize_10_ v).f_elements 10 in
     (forall (i: nat {i < 160}). inputs i == outputs i)
   ) =
  _ by (Tactics.GetBit.prove_bit_vector_equality' ())

#pop-options

#push-options "--z3rlimit 300"

let deserialize_10_lemma inputs =
  deserialize_10_bit_vec_lemma inputs;
  BitVecEq.bit_vec_equal_intro (bit_vec_of_int_t_array (deserialize_10_ inputs).f_elements 10) 
    (BitVecEq.retype (bit_vec_of_int_t_array inputs 8))

#pop-options

let deserialize_10_bounded_lemma inputs =
  admit()

let deserialize_11_ (bytes: t_Slice u8) =
  let v0_7_:(i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16) =
    deserialize_11_int (bytes.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 11 }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let v8_15_:(i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16) =
    deserialize_11_int (bytes.[ { Core.Ops.Range.f_start = sz 11; Core.Ops.Range.f_end = sz 22 }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  {
    Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
    =
    let list =
      [
        v0_7_._1; v0_7_._2; v0_7_._3; v0_7_._4; v0_7_._5; v0_7_._6; v0_7_._7; v0_7_._8; v8_15_._1;
        v8_15_._2; v8_15_._3; v8_15_._4; v8_15_._5; v8_15_._6; v8_15_._7; v8_15_._8
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
    Rust_primitives.Hax.array_of_list 16 list
  }
  <:
  Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector

let deserialize_12_ (bytes: t_Slice u8) =
  let v0_1_:(i16 & i16) =
    deserialize_12_int (bytes.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 3 }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let v2_3_:(i16 & i16) =
    deserialize_12_int (bytes.[ { Core.Ops.Range.f_start = sz 3; Core.Ops.Range.f_end = sz 6 }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let v4_5_:(i16 & i16) =
    deserialize_12_int (bytes.[ { Core.Ops.Range.f_start = sz 6; Core.Ops.Range.f_end = sz 9 }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let v6_7_:(i16 & i16) =
    deserialize_12_int (bytes.[ { Core.Ops.Range.f_start = sz 9; Core.Ops.Range.f_end = sz 12 }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let v8_9_:(i16 & i16) =
    deserialize_12_int (bytes.[ { Core.Ops.Range.f_start = sz 12; Core.Ops.Range.f_end = sz 15 }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let v10_11_:(i16 & i16) =
    deserialize_12_int (bytes.[ { Core.Ops.Range.f_start = sz 15; Core.Ops.Range.f_end = sz 18 }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let v12_13_:(i16 & i16) =
    deserialize_12_int (bytes.[ { Core.Ops.Range.f_start = sz 18; Core.Ops.Range.f_end = sz 21 }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let v14_15_:(i16 & i16) =
    deserialize_12_int (bytes.[ { Core.Ops.Range.f_start = sz 21; Core.Ops.Range.f_end = sz 24 }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  {
    Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
    =
    let list =
      [
        v0_1_._1; v0_1_._2; v2_3_._1; v2_3_._2; v4_5_._1; v4_5_._2; v6_7_._1; v6_7_._2; v8_9_._1;
        v8_9_._2; v10_11_._1; v10_11_._2; v12_13_._1; v12_13_._2; v14_15_._1; v14_15_._2
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
    Rust_primitives.Hax.array_of_list 16 list
  }
  <:
  Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector

#push-options "--compat_pre_core 2 --z3rlimit 300 --z3refresh"

let deserialize_12_bit_vec_lemma (v: t_Array u8 (sz 24))
   : squash (
     let inputs = bit_vec_of_int_t_array v 8 in
     let outputs = bit_vec_of_int_t_array (deserialize_12_ v).f_elements 12 in
     (forall (i: nat {i < 192}). inputs i == outputs i)
   ) =
  _ by (Tactics.GetBit.prove_bit_vector_equality' ())

#pop-options

#push-options "--z3rlimit 300"

let deserialize_12_lemma inputs =
  deserialize_12_bit_vec_lemma inputs;
  BitVecEq.bit_vec_equal_intro (bit_vec_of_int_t_array (deserialize_12_ inputs).f_elements 12) 
    (BitVecEq.retype (bit_vec_of_int_t_array inputs 8))

#pop-options

let deserialize_12_bounded_lemma inputs =
  admit()

let deserialize_4_ (bytes: t_Slice u8) =
  let v0_7_:(i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16) =
    deserialize_4_int (bytes.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 4 }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let v8_15_:(i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16) =
    deserialize_4_int (bytes.[ { Core.Ops.Range.f_start = sz 4; Core.Ops.Range.f_end = sz 8 }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  {
    Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
    =
    let list =
      [
        v0_7_._1; v0_7_._2; v0_7_._3; v0_7_._4; v0_7_._5; v0_7_._6; v0_7_._7; v0_7_._8; v8_15_._1;
        v8_15_._2; v8_15_._3; v8_15_._4; v8_15_._5; v8_15_._6; v8_15_._7; v8_15_._8
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
    Rust_primitives.Hax.array_of_list 16 list
  }
  <:
  Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector

#push-options "--compat_pre_core 2 --z3rlimit 300 --z3refresh"

let deserialize_4_bit_vec_lemma (v: t_Array u8 (sz 8))
   : squash (
     let inputs = bit_vec_of_int_t_array v 8 in
     let outputs = bit_vec_of_int_t_array (deserialize_4_ v).f_elements 4 in
     (forall (i: nat {i < 64}). inputs i == outputs i)
   ) =
  _ by (Tactics.GetBit.prove_bit_vector_equality' ())

#pop-options

#push-options "--z3rlimit 300"

let deserialize_4_lemma inputs =
  deserialize_4_bit_vec_lemma inputs;
  BitVecEq.bit_vec_equal_intro (bit_vec_of_int_t_array (deserialize_4_ inputs).f_elements 4) 
    (BitVecEq.retype (bit_vec_of_int_t_array inputs 8))

#pop-options

let deserialize_4_bounded_lemma inputs =
  admit()

let deserialize_5_ (bytes: t_Slice u8) =
  let v0_7_:(i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16) =
    deserialize_5_int (bytes.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 5 }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let v8_15_:(i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16) =
    deserialize_5_int (bytes.[ { Core.Ops.Range.f_start = sz 5; Core.Ops.Range.f_end = sz 10 }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  {
    Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
    =
    let list =
      [
        v0_7_._1; v0_7_._2; v0_7_._3; v0_7_._4; v0_7_._5; v0_7_._6; v0_7_._7; v0_7_._8; v8_15_._1;
        v8_15_._2; v8_15_._3; v8_15_._4; v8_15_._5; v8_15_._6; v8_15_._7; v8_15_._8
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
    Rust_primitives.Hax.array_of_list 16 list
  }
  <:
  Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector

let serialize_1_ (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  let result0:u8 =
    (((((((cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 0 ] <: i16) <: u8) |.
                ((cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 1 ] <: i16)
                    <:
                    u8) <<!
                  1l
                  <:
                  u8)
                <:
                u8) |.
              ((cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 2 ] <: i16) <: u8
                ) <<!
                2l
                <:
                u8)
              <:
              u8) |.
            ((cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 3 ] <: i16) <: u8) <<!
              3l
              <:
              u8)
            <:
            u8) |.
          ((cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 4 ] <: i16) <: u8) <<!
            4l
            <:
            u8)
          <:
          u8) |.
        ((cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 5 ] <: i16) <: u8) <<!
          5l
          <:
          u8)
        <:
        u8) |.
      ((cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 6 ] <: i16) <: u8) <<! 6l
        <:
        u8)
      <:
      u8) |.
    ((cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 7 ] <: i16) <: u8) <<! 7l
      <:
      u8)
  in
  let result1:u8 =
    (((((((cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 ] <: i16) <: u8) |.
                ((cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 9 ] <: i16)
                    <:
                    u8) <<!
                  1l
                  <:
                  u8)
                <:
                u8) |.
              ((cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 10 ] <: i16)
                  <:
                  u8) <<!
                2l
                <:
                u8)
              <:
              u8) |.
            ((cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 11 ] <: i16) <: u8) <<!
              3l
              <:
              u8)
            <:
            u8) |.
          ((cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 12 ] <: i16) <: u8) <<!
            4l
            <:
            u8)
          <:
          u8) |.
        ((cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 13 ] <: i16) <: u8) <<!
          5l
          <:
          u8)
        <:
        u8) |.
      ((cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 14 ] <: i16) <: u8) <<!
        6l
        <:
        u8)
      <:
      u8) |.
    ((cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 15 ] <: i16) <: u8) <<! 7l
      <:
      u8)
  in
  let list = [result0; result1] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
  Rust_primitives.Hax.array_of_list 2 list

#push-options "--compat_pre_core 2 --z3rlimit 300 --z3refresh"

let serialize_1_bit_vec_lemma (v: t_Array i16 (sz 16))
  (_: squash (forall i. Rust_primitives.bounded (Seq.index v i) 1))
   : squash (
     let inputs = bit_vec_of_int_t_array v 1 in
     let outputs = bit_vec_of_int_t_array (serialize_1_ ({ f_elements = v })) 8 in
     (forall (i: nat {i < 16}). inputs i == outputs i)
   ) =
  _ by (Tactics.GetBit.prove_bit_vector_equality' ())

#pop-options

#push-options "--z3rlimit 300"

let serialize_1_lemma inputs =
  serialize_1_bit_vec_lemma inputs.f_elements ();
  BitVecEq.bit_vec_equal_intro (bit_vec_of_int_t_array (serialize_1_ inputs) 8) 
    (BitVecEq.retype (bit_vec_of_int_t_array inputs.f_elements 1))

#pop-options

let serialize_10_ (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  let r0_4_:(u8 & u8 & u8 & u8 & u8) =
    serialize_10_int (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
            Core.Ops.Range.f_start = sz 0;
            Core.Ops.Range.f_end = sz 4
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let r5_9_:(u8 & u8 & u8 & u8 & u8) =
    serialize_10_int (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
            Core.Ops.Range.f_start = sz 4;
            Core.Ops.Range.f_end = sz 8
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let r10_14_:(u8 & u8 & u8 & u8 & u8) =
    serialize_10_int (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
            Core.Ops.Range.f_start = sz 8;
            Core.Ops.Range.f_end = sz 12
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let r15_19_:(u8 & u8 & u8 & u8 & u8) =
    serialize_10_int (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
            Core.Ops.Range.f_start = sz 12;
            Core.Ops.Range.f_end = sz 16
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let list =
    [
      r0_4_._1; r0_4_._2; r0_4_._3; r0_4_._4; r0_4_._5; r5_9_._1; r5_9_._2; r5_9_._3; r5_9_._4;
      r5_9_._5; r10_14_._1; r10_14_._2; r10_14_._3; r10_14_._4; r10_14_._5; r15_19_._1; r15_19_._2;
      r15_19_._3; r15_19_._4; r15_19_._5
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 20);
  Rust_primitives.Hax.array_of_list 20 list

#push-options "--compat_pre_core 2 --z3rlimit 300 --z3refresh"

let serialize_10_bit_vec_lemma (v: t_Array i16 (sz 16))
  (_: squash (forall i. Rust_primitives.bounded (Seq.index v i) 10))
   : squash (
     let inputs = bit_vec_of_int_t_array v 10 in
     let outputs = bit_vec_of_int_t_array (serialize_10_ ({ f_elements = v })) 8 in
     (forall (i: nat {i < 160}). inputs i == outputs i)
   ) =
  _ by (Tactics.GetBit.prove_bit_vector_equality' ())

#pop-options

#push-options "--z3rlimit 300"

let serialize_10_lemma inputs =
  serialize_10_bit_vec_lemma inputs.f_elements ();
  BitVecEq.bit_vec_equal_intro (bit_vec_of_int_t_array (serialize_10_ inputs) 8) 
    (BitVecEq.retype (bit_vec_of_int_t_array inputs.f_elements 10))

#pop-options

let serialize_11_ (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  let r0_10_:(u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8) =
    serialize_11_int (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
            Core.Ops.Range.f_start = sz 0;
            Core.Ops.Range.f_end = sz 8
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let r11_21_:(u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8) =
    serialize_11_int (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
            Core.Ops.Range.f_start = sz 8;
            Core.Ops.Range.f_end = sz 16
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let list =
    [
      r0_10_._1; r0_10_._2; r0_10_._3; r0_10_._4; r0_10_._5; r0_10_._6; r0_10_._7; r0_10_._8;
      r0_10_._9; r0_10_._10; r0_10_._11; r11_21_._1; r11_21_._2; r11_21_._3; r11_21_._4; r11_21_._5;
      r11_21_._6; r11_21_._7; r11_21_._8; r11_21_._9; r11_21_._10; r11_21_._11
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 22);
  Rust_primitives.Hax.array_of_list 22 list

let serialize_12_ (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  let r0_2_:(u8 & u8 & u8) =
    serialize_12_int (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
            Core.Ops.Range.f_start = sz 0;
            Core.Ops.Range.f_end = sz 2
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let r3_5_:(u8 & u8 & u8) =
    serialize_12_int (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
            Core.Ops.Range.f_start = sz 2;
            Core.Ops.Range.f_end = sz 4
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let r6_8_:(u8 & u8 & u8) =
    serialize_12_int (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
            Core.Ops.Range.f_start = sz 4;
            Core.Ops.Range.f_end = sz 6
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let r9_11_:(u8 & u8 & u8) =
    serialize_12_int (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
            Core.Ops.Range.f_start = sz 6;
            Core.Ops.Range.f_end = sz 8
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let r12_14_:(u8 & u8 & u8) =
    serialize_12_int (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
            Core.Ops.Range.f_start = sz 8;
            Core.Ops.Range.f_end = sz 10
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let r15_17_:(u8 & u8 & u8) =
    serialize_12_int (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
            Core.Ops.Range.f_start = sz 10;
            Core.Ops.Range.f_end = sz 12
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let r18_20_:(u8 & u8 & u8) =
    serialize_12_int (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
            Core.Ops.Range.f_start = sz 12;
            Core.Ops.Range.f_end = sz 14
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let r21_23_:(u8 & u8 & u8) =
    serialize_12_int (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
            Core.Ops.Range.f_start = sz 14;
            Core.Ops.Range.f_end = sz 16
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let list =
    [
      r0_2_._1; r0_2_._2; r0_2_._3; r3_5_._1; r3_5_._2; r3_5_._3; r6_8_._1; r6_8_._2; r6_8_._3;
      r9_11_._1; r9_11_._2; r9_11_._3; r12_14_._1; r12_14_._2; r12_14_._3; r15_17_._1; r15_17_._2;
      r15_17_._3; r18_20_._1; r18_20_._2; r18_20_._3; r21_23_._1; r21_23_._2; r21_23_._3
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 24);
  Rust_primitives.Hax.array_of_list 24 list

#push-options "--compat_pre_core 2 --z3rlimit 300 --z3refresh"

let serialize_12_bit_vec_lemma (v: t_Array i16 (sz 16))
  (_: squash (forall i. Rust_primitives.bounded (Seq.index v i) 12))
   : squash (
     let inputs = bit_vec_of_int_t_array v 12 in
     let outputs = bit_vec_of_int_t_array (serialize_12_ ({ f_elements = v })) 8 in
     (forall (i: nat {i < 192}). inputs i == outputs i)
   ) =
  _ by (Tactics.GetBit.prove_bit_vector_equality' ())

#pop-options

#push-options "--z3rlimit 300"

let serialize_12_lemma inputs =
  serialize_12_bit_vec_lemma inputs.f_elements ();
  BitVecEq.bit_vec_equal_intro (bit_vec_of_int_t_array (serialize_12_ inputs) 8) 
    (BitVecEq.retype (bit_vec_of_int_t_array inputs.f_elements 12))

#pop-options

let serialize_4_ (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  let result0_3_:(u8 & u8 & u8 & u8) =
    serialize_4_int (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
            Core.Ops.Range.f_start = sz 0;
            Core.Ops.Range.f_end = sz 8
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let result4_7_:(u8 & u8 & u8 & u8) =
    serialize_4_int (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
            Core.Ops.Range.f_start = sz 8;
            Core.Ops.Range.f_end = sz 16
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let list =
    [
      result0_3_._1;
      result0_3_._2;
      result0_3_._3;
      result0_3_._4;
      result4_7_._1;
      result4_7_._2;
      result4_7_._3;
      result4_7_._4
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
  Rust_primitives.Hax.array_of_list 8 list

#push-options "--compat_pre_core 2 --z3rlimit 300 --z3refresh"

let serialize_4_bit_vec_lemma (v: t_Array i16 (sz 16))
  (_: squash (forall i. Rust_primitives.bounded (Seq.index v i) 4))
   : squash (
     let inputs = bit_vec_of_int_t_array v 4 in
     let outputs = bit_vec_of_int_t_array (serialize_4_ ({ f_elements = v })) 8 in
     (forall (i: nat {i < 64}). inputs i == outputs i)
   ) =
  _ by (Tactics.GetBit.prove_bit_vector_equality' ())

#pop-options

#push-options "--z3rlimit 300"

let serialize_4_lemma inputs =
  serialize_4_bit_vec_lemma inputs.f_elements ();
  BitVecEq.bit_vec_equal_intro (bit_vec_of_int_t_array (serialize_4_ inputs) 8) 
    (BitVecEq.retype (bit_vec_of_int_t_array inputs.f_elements 4))

#pop-options

let serialize_5_ (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  let r0_4_:(u8 & u8 & u8 & u8 & u8) =
    serialize_5_int (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
            Core.Ops.Range.f_start = sz 0;
            Core.Ops.Range.f_end = sz 8
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let r5_9_:(u8 & u8 & u8 & u8 & u8) =
    serialize_5_int (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
            Core.Ops.Range.f_start = sz 8;
            Core.Ops.Range.f_end = sz 16
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let list =
    [
      r0_4_._1; r0_4_._2; r0_4_._3; r0_4_._4; r0_4_._5; r5_9_._1; r5_9_._2; r5_9_._3; r5_9_._4;
      r5_9_._5
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 10);
  Rust_primitives.Hax.array_of_list 10 list
