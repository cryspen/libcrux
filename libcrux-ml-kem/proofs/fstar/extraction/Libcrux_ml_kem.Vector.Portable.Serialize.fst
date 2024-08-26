module Libcrux_ml_kem.Vector.Portable.Serialize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
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

let serialize_1_ (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  let result:t_Array u8 (sz 2) = Rust_primitives.Hax.repeat 0uy (sz 2) in
  let result:t_Array u8 (sz 2) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (sz 8)
      (fun result temp_1_ ->
          let result:t_Array u8 (sz 2) = result in
          let _:usize = temp_1_ in
          true)
      result
      (fun result i ->
          let result:t_Array u8 (sz 2) = result in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
            (sz 0)
            ((result.[ sz 0 ] <: u8) |.
              ((cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16) <: u8) <<!
                i
                <:
                u8)
              <:
              u8)
          <:
          t_Array u8 (sz 2))
  in
  let result:t_Array u8 (sz 2) =
    Rust_primitives.Hax.Folds.fold_range (sz 8)
      (sz 16)
      (fun result temp_1_ ->
          let result:t_Array u8 (sz 2) = result in
          let _:usize = temp_1_ in
          true)
      result
      (fun result i ->
          let result:t_Array u8 (sz 2) = result in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
            (sz 1)
            ((result.[ sz 1 ] <: u8) |.
              ((cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16) <: u8) <<!
                (i -! sz 8 <: usize)
                <:
                u8)
              <:
              u8)
          <:
          t_Array u8 (sz 2))
  in
  result

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
  let result:t_Array u8 (sz 20) = Rust_primitives.Hax.repeat 0uy (sz 20) in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 0) r0_4_._1
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 1) r0_4_._2
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 2) r0_4_._3
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 3) r0_4_._4
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 4) r0_4_._5
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 5) r5_9_._1
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 6) r5_9_._2
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 7) r5_9_._3
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 8) r5_9_._4
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 9) r5_9_._5
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 10) r10_14_._1
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 11) r10_14_._2
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 12) r10_14_._3
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 13) r10_14_._4
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 14) r10_14_._5
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 15) r15_19_._1
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 16) r15_19_._2
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 17) r15_19_._3
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 18) r15_19_._4
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 19) r15_19_._5
  in
  result

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
  let result:t_Array u8 (sz 22) = Rust_primitives.Hax.repeat 0uy (sz 22) in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 0) r0_10_._1
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 1) r0_10_._2
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 2) r0_10_._3
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 3) r0_10_._4
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 4) r0_10_._5
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 5) r0_10_._6
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 6) r0_10_._7
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 7) r0_10_._8
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 8) r0_10_._9
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 9) r0_10_._10
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 10) r0_10_._11
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 11) r11_21_._1
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 12) r11_21_._2
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 13) r11_21_._3
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 14) r11_21_._4
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 15) r11_21_._5
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 16) r11_21_._6
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 17) r11_21_._7
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 18) r11_21_._8
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 19) r11_21_._9
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 20) r11_21_._10
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 21) r11_21_._11
  in
  result

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
  let result:t_Array u8 (sz 24) = Rust_primitives.Hax.repeat 0uy (sz 24) in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 0) r0_2_._1
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 1) r0_2_._2
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 2) r0_2_._3
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 3) r3_5_._1
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 4) r3_5_._2
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 5) r3_5_._3
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 6) r6_8_._1
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 7) r6_8_._2
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 8) r6_8_._3
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 9) r9_11_._1
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 10) r9_11_._2
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 11) r9_11_._3
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 12) r12_14_._1
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 13) r12_14_._2
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 14) r12_14_._3
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 15) r15_17_._1
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 16) r15_17_._2
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 17) r15_17_._3
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 18) r18_20_._1
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 19) r18_20_._2
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 20) r18_20_._3
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 21) r21_23_._1
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 22) r21_23_._2
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 23) r21_23_._3
  in
  result

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
  let result:t_Array u8 (sz 8) = Rust_primitives.Hax.repeat 0uy (sz 8) in
  let result:t_Array u8 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 0) result0_3_._1
  in
  let result:t_Array u8 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 1) result0_3_._2
  in
  let result:t_Array u8 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 2) result0_3_._3
  in
  let result:t_Array u8 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 3) result0_3_._4
  in
  let result:t_Array u8 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 4) result4_7_._1
  in
  let result:t_Array u8 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 5) result4_7_._2
  in
  let result:t_Array u8 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 6) result4_7_._3
  in
  let result:t_Array u8 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 7) result4_7_._4
  in
  result

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
  let result:t_Array u8 (sz 10) = Rust_primitives.Hax.repeat 0uy (sz 10) in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 0) r0_4_._1
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 1) r0_4_._2
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 2) r0_4_._3
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 3) r0_4_._4
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 4) r0_4_._5
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 5) r5_9_._1
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 6) r5_9_._2
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 7) r5_9_._3
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 8) r5_9_._4
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 9) r5_9_._5
  in
  result

let deserialize_1_ (v: t_Slice u8) =
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Libcrux_ml_kem.Vector.Portable.Vector_type.zero ()
  in
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (sz 8)
      (fun result temp_1_ ->
          let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = result in
          let _:usize = temp_1_ in
          true)
      result
      (fun result i ->
          let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = result in
          let i:usize = i in
          {
            result with
            Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
                .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
              i
              (cast (((v.[ sz 0 ] <: u8) >>! i <: u8) &. 1uy <: u8) <: i16)
            <:
            t_Array i16 (sz 16)
          }
          <:
          Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
  in
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Rust_primitives.Hax.Folds.fold_range (sz 8)
      Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
      (fun result temp_1_ ->
          let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = result in
          let _:usize = temp_1_ in
          true)
      result
      (fun result i ->
          let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = result in
          let i:usize = i in
          {
            result with
            Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
                .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
              i
              (cast (((v.[ sz 1 ] <: u8) >>! (i -! sz 8 <: usize) <: u8) &. 1uy <: u8) <: i16)
            <:
            t_Array i16 (sz 16)
          }
          <:
          Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
  in
  result

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
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Libcrux_ml_kem.Vector.Portable.Vector_type.zero ()
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 0)
        v0_7_._1
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 1)
        v0_7_._2
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 2)
        v0_7_._3
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 3)
        v0_7_._4
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 4)
        v0_7_._5
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 5)
        v0_7_._6
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 6)
        v0_7_._7
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 7)
        v0_7_._8
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8)
        v8_15_._1
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 9)
        v8_15_._2
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 10)
        v8_15_._3
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 11)
        v8_15_._4
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 12)
        v8_15_._5
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 13)
        v8_15_._6
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 14)
        v8_15_._7
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 15)
        v8_15_._8
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  v

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
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Libcrux_ml_kem.Vector.Portable.Vector_type.zero ()
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 0)
        v0_7_._1
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 1)
        v0_7_._2
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 2)
        v0_7_._3
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 3)
        v0_7_._4
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 4)
        v0_7_._5
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 5)
        v0_7_._6
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 6)
        v0_7_._7
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 7)
        v0_7_._8
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8)
        v8_15_._1
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 9)
        v8_15_._2
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 10)
        v8_15_._3
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 11)
        v8_15_._4
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 12)
        v8_15_._5
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 13)
        v8_15_._6
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 14)
        v8_15_._7
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 15)
        v8_15_._8
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  v

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
  let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Libcrux_ml_kem.Vector.Portable.Vector_type.zero ()
  in
  let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      re with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 0)
        v0_1_._1
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      re with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 1)
        v0_1_._2
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      re with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 2)
        v2_3_._1
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      re with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 3)
        v2_3_._2
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      re with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 4)
        v4_5_._1
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      re with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 5)
        v4_5_._2
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      re with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 6)
        v6_7_._1
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      re with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 7)
        v6_7_._2
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      re with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8)
        v8_9_._1
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      re with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 9)
        v8_9_._2
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      re with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 10)
        v10_11_._1
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      re with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 11)
        v10_11_._2
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      re with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 12)
        v12_13_._1
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      re with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 13)
        v12_13_._2
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      re with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 14)
        v14_15_._1
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      re with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 15)
        v14_15_._2
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  re

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
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Libcrux_ml_kem.Vector.Portable.Vector_type.zero ()
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 0)
        v0_7_._1
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 1)
        v0_7_._2
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 2)
        v0_7_._3
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 3)
        v0_7_._4
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 4)
        v0_7_._5
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 5)
        v0_7_._6
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 6)
        v0_7_._7
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 7)
        v0_7_._8
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8)
        v8_15_._1
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 9)
        v8_15_._2
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 10)
        v8_15_._3
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 11)
        v8_15_._4
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 12)
        v8_15_._5
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 13)
        v8_15_._6
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 14)
        v8_15_._7
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 15)
        v8_15_._8
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  v

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
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Libcrux_ml_kem.Vector.Portable.Vector_type.zero ()
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 0)
        v0_7_._1
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 1)
        v0_7_._2
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 2)
        v0_7_._3
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 3)
        v0_7_._4
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 4)
        v0_7_._5
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 5)
        v0_7_._6
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 6)
        v0_7_._7
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 7)
        v0_7_._8
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8)
        v8_15_._1
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 9)
        v8_15_._2
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 10)
        v8_15_._3
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 11)
        v8_15_._4
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 12)
        v8_15_._5
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 13)
        v8_15_._6
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 14)
        v8_15_._7
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 15)
        v8_15_._8
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  v
