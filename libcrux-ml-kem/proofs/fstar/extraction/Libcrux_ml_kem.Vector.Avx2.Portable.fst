module Libcrux_ml_kem.Vector.Avx2.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

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

let from_i16_array (array: t_Array i16 (sz 16)) = { f_elements = array } <: t_PortableVector

let serialize_11_ (v: t_PortableVector) =
  let r0_10_:(u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8) =
    serialize_11_int (v.f_elements.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 8 }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let r11_21_:(u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8) =
    serialize_11_int (v.f_elements.[ { Core.Ops.Range.f_start = sz 8; Core.Ops.Range.f_end = sz 16 }
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

let to_i16_array (v: t_PortableVector) = v.f_elements

let zero (_: Prims.unit) =
  { f_elements = Rust_primitives.Hax.repeat 0s (sz 16) } <: t_PortableVector

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
  let v:t_PortableVector = zero () in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements (sz 0) v0_7_._1
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements (sz 1) v0_7_._2
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements (sz 2) v0_7_._3
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements (sz 3) v0_7_._4
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements (sz 4) v0_7_._5
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements (sz 5) v0_7_._6
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements (sz 6) v0_7_._7
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements (sz 7) v0_7_._8
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements (sz 8) v8_15_._1
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements (sz 9) v8_15_._2
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements (sz 10) v8_15_._3
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements (sz 11) v8_15_._4
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements (sz 12) v8_15_._5
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements (sz 13) v8_15_._6
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements (sz 14) v8_15_._7
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements (sz 15) v8_15_._8
    }
    <:
    t_PortableVector
  in
  v
