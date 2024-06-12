module Libcrux_ml_kem.Vector.Avx2.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let from_i16_array (array: t_Array i16 (sz 16)) = { f_elements = array } <: t_PortableVector

let serialize_11_ (v: t_PortableVector) =
  let result:t_Array u8 (sz 22) = Rust_primitives.Hax.repeat 0uy (sz 22) in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 0)
      (cast (v.f_elements.[ sz 0 ] <: i16) <: u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 1)
      (((cast ((v.f_elements.[ sz 1 ] <: i16) &. 31s <: i16) <: u8) <<! 3l <: u8) |.
        (cast ((v.f_elements.[ sz 0 ] <: i16) >>! 8l <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 2)
      (((cast ((v.f_elements.[ sz 2 ] <: i16) &. 3s <: i16) <: u8) <<! 6l <: u8) |.
        (cast ((v.f_elements.[ sz 1 ] <: i16) >>! 5l <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 3)
      (cast (((v.f_elements.[ sz 2 ] <: i16) >>! 2l <: i16) &. 255s <: i16) <: u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 4)
      (((cast ((v.f_elements.[ sz 3 ] <: i16) &. 127s <: i16) <: u8) <<! 1l <: u8) |.
        (cast ((v.f_elements.[ sz 2 ] <: i16) >>! 10l <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 5)
      (((cast ((v.f_elements.[ sz 4 ] <: i16) &. 15s <: i16) <: u8) <<! 4l <: u8) |.
        (cast ((v.f_elements.[ sz 3 ] <: i16) >>! 7l <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 6)
      (((cast ((v.f_elements.[ sz 5 ] <: i16) &. 1s <: i16) <: u8) <<! 7l <: u8) |.
        (cast ((v.f_elements.[ sz 4 ] <: i16) >>! 4l <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 7)
      (cast (((v.f_elements.[ sz 5 ] <: i16) >>! 1l <: i16) &. 255s <: i16) <: u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 8)
      (((cast ((v.f_elements.[ sz 6 ] <: i16) &. 63s <: i16) <: u8) <<! 2l <: u8) |.
        (cast ((v.f_elements.[ sz 5 ] <: i16) >>! 9l <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 9)
      (((cast ((v.f_elements.[ sz 7 ] <: i16) &. 7s <: i16) <: u8) <<! 5l <: u8) |.
        (cast ((v.f_elements.[ sz 6 ] <: i16) >>! 6l <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 10)
      (cast ((v.f_elements.[ sz 7 ] <: i16) >>! 3l <: i16) <: u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 11)
      (cast (v.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16) <: u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 12)
      (((cast ((v.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16) &. 31s <: i16) <: u8) <<! 3l <: u8) |.
        (cast ((v.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16) >>! 8l <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 13)
      (((cast ((v.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16) &. 3s <: i16) <: u8) <<! 6l <: u8) |.
        (cast ((v.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16) >>! 5l <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 14)
      (cast (((v.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16) >>! 2l <: i16) &. 255s <: i16) <: u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 15)
      (((cast ((v.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16) &. 127s <: i16) <: u8) <<! 1l <: u8) |.
        (cast ((v.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16) >>! 10l <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 16)
      (((cast ((v.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16) &. 15s <: i16) <: u8) <<! 4l <: u8) |.
        (cast ((v.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16) >>! 7l <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 17)
      (((cast ((v.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16) &. 1s <: i16) <: u8) <<! 7l <: u8) |.
        (cast ((v.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16) >>! 4l <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 18)
      (cast (((v.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16) >>! 1l <: i16) &. 255s <: i16) <: u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 19)
      (((cast ((v.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16) &. 63s <: i16) <: u8) <<! 2l <: u8) |.
        (cast ((v.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16) >>! 9l <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 20)
      (((cast ((v.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16) &. 7s <: i16) <: u8) <<! 5l <: u8) |.
        (cast ((v.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16) >>! 6l <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 21)
      (cast ((v.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16) >>! 3l <: i16) <: u8)
  in
  result

let to_i16_array (v: t_PortableVector) = v.f_elements

let zero (_: Prims.unit) =
  { f_elements = Rust_primitives.Hax.repeat 0s (sz 16) } <: t_PortableVector

let deserialize_11_ (bytes: t_Slice u8) =
  let result:t_PortableVector = zero () in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 0)
        ((((cast (bytes.[ sz 1 ] <: u8) <: i16) &. 7s <: i16) <<! 8l <: i16) |.
          (cast (bytes.[ sz 0 ] <: u8) <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 1)
        ((((cast (bytes.[ sz 2 ] <: u8) <: i16) &. 63s <: i16) <<! 5l <: i16) |.
          ((cast (bytes.[ sz 1 ] <: u8) <: i16) >>! 3l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 2)
        (((((cast (bytes.[ sz 4 ] <: u8) <: i16) &. 1s <: i16) <<! 10l <: i16) |.
            ((cast (bytes.[ sz 3 ] <: u8) <: i16) <<! 2l <: i16)
            <:
            i16) |.
          ((cast (bytes.[ sz 2 ] <: u8) <: i16) >>! 6l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 3)
        ((((cast (bytes.[ sz 5 ] <: u8) <: i16) &. 15s <: i16) <<! 7l <: i16) |.
          ((cast (bytes.[ sz 4 ] <: u8) <: i16) >>! 1l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 4)
        ((((cast (bytes.[ sz 6 ] <: u8) <: i16) &. 127s <: i16) <<! 4l <: i16) |.
          ((cast (bytes.[ sz 5 ] <: u8) <: i16) >>! 4l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 5)
        (((((cast (bytes.[ sz 8 ] <: u8) <: i16) &. 3s <: i16) <<! 9l <: i16) |.
            ((cast (bytes.[ sz 7 ] <: u8) <: i16) <<! 1l <: i16)
            <:
            i16) |.
          ((cast (bytes.[ sz 6 ] <: u8) <: i16) >>! 7l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 6)
        ((((cast (bytes.[ sz 9 ] <: u8) <: i16) &. 31s <: i16) <<! 6l <: i16) |.
          ((cast (bytes.[ sz 8 ] <: u8) <: i16) >>! 2l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 7)
        (((cast (bytes.[ sz 10 ] <: u8) <: i16) <<! 3l <: i16) |.
          ((cast (bytes.[ sz 9 ] <: u8) <: i16) >>! 5l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 8)
        ((((cast (bytes.[ sz 11 +! sz 1 <: usize ] <: u8) <: i16) &. 7s <: i16) <<! 8l <: i16) |.
          (cast (bytes.[ sz 11 +! sz 0 <: usize ] <: u8) <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 9)
        ((((cast (bytes.[ sz 11 +! sz 2 <: usize ] <: u8) <: i16) &. 63s <: i16) <<! 5l <: i16) |.
          ((cast (bytes.[ sz 11 +! sz 1 <: usize ] <: u8) <: i16) >>! 3l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 10)
        (((((cast (bytes.[ sz 11 +! sz 4 <: usize ] <: u8) <: i16) &. 1s <: i16) <<! 10l <: i16) |.
            ((cast (bytes.[ sz 11 +! sz 3 <: usize ] <: u8) <: i16) <<! 2l <: i16)
            <:
            i16) |.
          ((cast (bytes.[ sz 11 +! sz 2 <: usize ] <: u8) <: i16) >>! 6l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 11)
        ((((cast (bytes.[ sz 11 +! sz 5 <: usize ] <: u8) <: i16) &. 15s <: i16) <<! 7l <: i16) |.
          ((cast (bytes.[ sz 11 +! sz 4 <: usize ] <: u8) <: i16) >>! 1l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 12)
        ((((cast (bytes.[ sz 11 +! sz 6 <: usize ] <: u8) <: i16) &. 127s <: i16) <<! 4l <: i16) |.
          ((cast (bytes.[ sz 11 +! sz 5 <: usize ] <: u8) <: i16) >>! 4l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 13)
        (((((cast (bytes.[ sz 11 +! sz 8 <: usize ] <: u8) <: i16) &. 3s <: i16) <<! 9l <: i16) |.
            ((cast (bytes.[ sz 11 +! sz 7 <: usize ] <: u8) <: i16) <<! 1l <: i16)
            <:
            i16) |.
          ((cast (bytes.[ sz 11 +! sz 6 <: usize ] <: u8) <: i16) >>! 7l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 14)
        ((((cast (bytes.[ sz 11 +! sz 9 <: usize ] <: u8) <: i16) &. 31s <: i16) <<! 6l <: i16) |.
          ((cast (bytes.[ sz 11 +! sz 8 <: usize ] <: u8) <: i16) >>! 2l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 15)
        (((cast (bytes.[ sz 11 +! sz 10 <: usize ] <: u8) <: i16) <<! 3l <: i16) |.
          ((cast (bytes.[ sz 11 +! sz 9 <: usize ] <: u8) <: i16) >>! 5l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  result
