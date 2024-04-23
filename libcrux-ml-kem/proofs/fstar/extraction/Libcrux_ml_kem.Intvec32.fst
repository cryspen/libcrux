module Libcrux_ml_kem.Intvec32
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let add_int_vec (lhs rhs: t_IntVec) =
  let lhs:t_IntVec =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_SIZE_VEC
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      lhs
      (fun lhs i ->
          let lhs:t_IntVec = lhs in
          let i:usize = i in
          {
            lhs with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize lhs.f_elements
              i
              ((lhs.f_elements.[ i ] <: i32) +! (rhs.f_elements.[ i ] <: i32) <: i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          t_IntVec)
  in
  lhs

let add_int_vec_constant (lhs: t_IntVec) (rhs: i32) =
  let lhs:t_IntVec =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_SIZE_VEC
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      lhs
      (fun lhs i ->
          let lhs:t_IntVec = lhs in
          let i:usize = i in
          {
            lhs with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize lhs.f_elements
              i
              ((lhs.f_elements.[ i ] <: i32) +! rhs <: i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          t_IntVec)
  in
  lhs

let barrett_reduce_int_vec (a: t_IntVec) =
  let a:t_IntVec =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_SIZE_VEC
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      a
      (fun a i ->
          let a:t_IntVec = a in
          let i:usize = i in
          {
            a with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
              i
              (Libcrux_ml_kem.Arithmetic.barrett_reduce (a.f_elements.[ i ] <: i32) <: i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          t_IntVec)
  in
  a

let bit_and_int_vec_constant (lhs: t_IntVec) (rhs: i32) =
  let lhs:t_IntVec =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_SIZE_VEC
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      lhs
      (fun lhs i ->
          let lhs:t_IntVec = lhs in
          let i:usize = i in
          {
            lhs with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize lhs.f_elements
              i
              ((lhs.f_elements.[ i ] <: i32) &. rhs <: i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          t_IntVec)
  in
  lhs

let compress_1_int_vec (a: t_IntVec) =
  let a:t_IntVec =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_SIZE_VEC
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      a
      (fun a i ->
          let a:t_IntVec = a in
          let i:usize = i in
          {
            a with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
              i
              (cast (Libcrux_ml_kem.Compress.compress_message_coefficient (cast (a.f_elements.[ i ]
                            <:
                            i32)
                        <:
                        u16)
                    <:
                    u8)
                <:
                i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          t_IntVec)
  in
  a

let compress_int_vec (coefficient_bits: u8) (a: t_IntVec) =
  let a:t_IntVec =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_SIZE_VEC
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      a
      (fun a i ->
          let a:t_IntVec = a in
          let i:usize = i in
          {
            a with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
              i
              (Libcrux_ml_kem.Compress.compress_ciphertext_coefficient coefficient_bits
                  (cast (a.f_elements.[ i ] <: i32) <: u16)
                <:
                i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          t_IntVec)
  in
  a

let deserialize_10_int_vec (bytes: t_Slice u8) =
  let result:t_IntVec = v_ZERO_VEC in
  let result:t_IntVec =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 0)
        ((((cast (bytes.[ sz 1 ] <: u8) <: i32) &. 3l <: i32) <<! 8l <: i32) |.
          ((cast (bytes.[ sz 0 ] <: u8) <: i32) &. 255l <: i32)
          <:
          i32)
    }
    <:
    t_IntVec
  in
  let result:t_IntVec =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 1)
        ((((cast (bytes.[ sz 2 ] <: u8) <: i32) &. 15l <: i32) <<! 6l <: i32) |.
          ((cast (bytes.[ sz 1 ] <: u8) <: i32) >>! 2l <: i32)
          <:
          i32)
    }
    <:
    t_IntVec
  in
  let result:t_IntVec =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 2)
        ((((cast (bytes.[ sz 3 ] <: u8) <: i32) &. 63l <: i32) <<! 4l <: i32) |.
          ((cast (bytes.[ sz 2 ] <: u8) <: i32) >>! 4l <: i32)
          <:
          i32)
    }
    <:
    t_IntVec
  in
  let result:t_IntVec =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 3)
        (((cast (bytes.[ sz 4 ] <: u8) <: i32) <<! 2l <: i32) |.
          ((cast (bytes.[ sz 3 ] <: u8) <: i32) >>! 6l <: i32)
          <:
          i32)
    }
    <:
    t_IntVec
  in
  let result:t_IntVec =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 4)
        ((((cast (bytes.[ sz 6 ] <: u8) <: i32) &. 3l <: i32) <<! 8l <: i32) |.
          ((cast (bytes.[ sz 5 ] <: u8) <: i32) &. 255l <: i32)
          <:
          i32)
    }
    <:
    t_IntVec
  in
  let result:t_IntVec =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 5)
        ((((cast (bytes.[ sz 7 ] <: u8) <: i32) &. 15l <: i32) <<! 6l <: i32) |.
          ((cast (bytes.[ sz 6 ] <: u8) <: i32) >>! 2l <: i32)
          <:
          i32)
    }
    <:
    t_IntVec
  in
  let result:t_IntVec =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 6)
        ((((cast (bytes.[ sz 8 ] <: u8) <: i32) &. 63l <: i32) <<! 4l <: i32) |.
          ((cast (bytes.[ sz 7 ] <: u8) <: i32) >>! 4l <: i32)
          <:
          i32)
    }
    <:
    t_IntVec
  in
  let result:t_IntVec =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 7)
        (((cast (bytes.[ sz 9 ] <: u8) <: i32) <<! 2l <: i32) |.
          ((cast (bytes.[ sz 8 ] <: u8) <: i32) >>! 6l <: i32)
          <:
          i32)
    }
    <:
    t_IntVec
  in
  result

let deserialize_11_int_vec (bytes: t_Slice u8) =
  let result:t_IntVec = v_ZERO_VEC in
  let result:t_IntVec =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 0)
        ((((cast (bytes.[ sz 1 ] <: u8) <: i32) &. 7l <: i32) <<! 8l <: i32) |.
          (cast (bytes.[ sz 0 ] <: u8) <: i32)
          <:
          i32)
    }
    <:
    t_IntVec
  in
  let result:t_IntVec =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 1)
        ((((cast (bytes.[ sz 2 ] <: u8) <: i32) &. 63l <: i32) <<! 5l <: i32) |.
          ((cast (bytes.[ sz 1 ] <: u8) <: i32) >>! 3l <: i32)
          <:
          i32)
    }
    <:
    t_IntVec
  in
  let result:t_IntVec =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 2)
        (((((cast (bytes.[ sz 4 ] <: u8) <: i32) &. 1l <: i32) <<! 10l <: i32) |.
            ((cast (bytes.[ sz 3 ] <: u8) <: i32) <<! 2l <: i32)
            <:
            i32) |.
          ((cast (bytes.[ sz 2 ] <: u8) <: i32) >>! 6l <: i32)
          <:
          i32)
    }
    <:
    t_IntVec
  in
  let result:t_IntVec =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 3)
        ((((cast (bytes.[ sz 5 ] <: u8) <: i32) &. 15l <: i32) <<! 7l <: i32) |.
          ((cast (bytes.[ sz 4 ] <: u8) <: i32) >>! 1l <: i32)
          <:
          i32)
    }
    <:
    t_IntVec
  in
  let result:t_IntVec =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 4)
        ((((cast (bytes.[ sz 6 ] <: u8) <: i32) &. 127l <: i32) <<! 4l <: i32) |.
          ((cast (bytes.[ sz 5 ] <: u8) <: i32) >>! 4l <: i32)
          <:
          i32)
    }
    <:
    t_IntVec
  in
  let result:t_IntVec =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 5)
        (((((cast (bytes.[ sz 8 ] <: u8) <: i32) &. 3l <: i32) <<! 9l <: i32) |.
            ((cast (bytes.[ sz 7 ] <: u8) <: i32) <<! 1l <: i32)
            <:
            i32) |.
          ((cast (bytes.[ sz 6 ] <: u8) <: i32) >>! 7l <: i32)
          <:
          i32)
    }
    <:
    t_IntVec
  in
  let result:t_IntVec =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 6)
        ((((cast (bytes.[ sz 9 ] <: u8) <: i32) &. 31l <: i32) <<! 6l <: i32) |.
          ((cast (bytes.[ sz 8 ] <: u8) <: i32) >>! 2l <: i32)
          <:
          i32)
    }
    <:
    t_IntVec
  in
  let result:t_IntVec =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 7)
        (((cast (bytes.[ sz 10 ] <: u8) <: i32) <<! 3l <: i32) |.
          ((cast (bytes.[ sz 9 ] <: u8) <: i32) >>! 5l <: i32)
          <:
          i32)
    }
    <:
    t_IntVec
  in
  result

let deserialize_12_int_vec (bytes: t_Slice u8) =
  let re:t_IntVec = v_ZERO_VEC in
  let byte0:i32 = cast (bytes.[ sz 0 ] <: u8) <: i32 in
  let byte1:i32 = cast (bytes.[ sz 1 ] <: u8) <: i32 in
  let byte2:i32 = cast (bytes.[ sz 2 ] <: u8) <: i32 in
  let byte3:i32 = cast (bytes.[ sz 3 ] <: u8) <: i32 in
  let byte4:i32 = cast (bytes.[ sz 4 ] <: u8) <: i32 in
  let byte5:i32 = cast (bytes.[ sz 5 ] <: u8) <: i32 in
  let byte6:i32 = cast (bytes.[ sz 6 ] <: u8) <: i32 in
  let byte7:i32 = cast (bytes.[ sz 7 ] <: u8) <: i32 in
  let byte8:i32 = cast (bytes.[ sz 8 ] <: u8) <: i32 in
  let byte9:i32 = cast (bytes.[ sz 9 ] <: u8) <: i32 in
  let byte10:i32 = cast (bytes.[ sz 10 ] <: u8) <: i32 in
  let byte11:i32 = cast (bytes.[ sz 11 ] <: u8) <: i32 in
  let re:t_IntVec =
    {
      re with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_elements
        (sz 0)
        (((byte1 &. 15l <: i32) <<! 8l <: i32) |. (byte0 &. 255l <: i32) <: i32)
    }
    <:
    t_IntVec
  in
  let re:t_IntVec =
    {
      re with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_elements
        (sz 1)
        ((byte2 <<! 4l <: i32) |. ((byte1 >>! 4l <: i32) &. 15l <: i32) <: i32)
    }
    <:
    t_IntVec
  in
  let re:t_IntVec =
    {
      re with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_elements
        (sz 2)
        (((byte4 &. 15l <: i32) <<! 8l <: i32) |. (byte3 &. 255l <: i32) <: i32)
    }
    <:
    t_IntVec
  in
  let re:t_IntVec =
    {
      re with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_elements
        (sz 3)
        ((byte5 <<! 4l <: i32) |. ((byte4 >>! 4l <: i32) &. 15l <: i32) <: i32)
    }
    <:
    t_IntVec
  in
  let re:t_IntVec =
    {
      re with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_elements
        (sz 4)
        (((byte7 &. 15l <: i32) <<! 8l <: i32) |. (byte6 &. 255l <: i32) <: i32)
    }
    <:
    t_IntVec
  in
  let re:t_IntVec =
    {
      re with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_elements
        (sz 5)
        ((byte8 <<! 4l <: i32) |. ((byte7 >>! 4l <: i32) &. 15l <: i32) <: i32)
    }
    <:
    t_IntVec
  in
  let re:t_IntVec =
    {
      re with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_elements
        (sz 6)
        (((byte10 &. 15l <: i32) <<! 8l <: i32) |. (byte9 &. 255l <: i32) <: i32)
    }
    <:
    t_IntVec
  in
  let re:t_IntVec =
    {
      re with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_elements
        (sz 7)
        ((byte11 <<! 4l <: i32) |. ((byte10 >>! 4l <: i32) &. 15l <: i32) <: i32)
    }
    <:
    t_IntVec
  in
  re

let deserialize_1_int_vec (a: u8) =
  let result:t_IntVec = v_ZERO_VEC in
  let result:t_IntVec =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_SIZE_VEC
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      result
      (fun result i ->
          let result:t_IntVec = result in
          let i:usize = i in
          {
            result with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
              i
              (cast ((a >>! i <: u8) &. 1uy <: u8) <: i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          t_IntVec)
  in
  result

let deserialize_4_int_vec (bytes: t_Slice u8) =
  let a:t_IntVec = v_ZERO_VEC in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 0)
        (cast ((bytes.[ sz 0 ] <: u8) &. 15uy <: u8) <: i32)
    }
    <:
    t_IntVec
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 1)
        (cast (((bytes.[ sz 0 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i32)
    }
    <:
    t_IntVec
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 2)
        (cast ((bytes.[ sz 1 ] <: u8) &. 15uy <: u8) <: i32)
    }
    <:
    t_IntVec
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 3)
        (cast (((bytes.[ sz 1 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i32)
    }
    <:
    t_IntVec
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 4)
        (cast ((bytes.[ sz 2 ] <: u8) &. 15uy <: u8) <: i32)
    }
    <:
    t_IntVec
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 5)
        (cast (((bytes.[ sz 2 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i32)
    }
    <:
    t_IntVec
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 6)
        (cast ((bytes.[ sz 3 ] <: u8) &. 15uy <: u8) <: i32)
    }
    <:
    t_IntVec
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 7)
        (cast (((bytes.[ sz 3 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i32)
    }
    <:
    t_IntVec
  in
  a

let deserialize_5_int_vec (bytes: t_Slice u8) =
  let a:t_IntVec = v_ZERO_VEC in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 0)
        (cast ((bytes.[ sz 0 ] <: u8) &. 31uy <: u8) <: i32)
    }
    <:
    t_IntVec
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 1)
        (cast ((((bytes.[ sz 1 ] <: u8) &. 3uy <: u8) <<! 3l <: u8) |.
              ((bytes.[ sz 0 ] <: u8) >>! 5l <: u8)
              <:
              u8)
          <:
          i32)
    }
    <:
    t_IntVec
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 2)
        (cast (((bytes.[ sz 1 ] <: u8) >>! 2l <: u8) &. 31uy <: u8) <: i32)
    }
    <:
    t_IntVec
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 3)
        (cast ((((bytes.[ sz 2 ] <: u8) &. 15uy <: u8) <<! 1l <: u8) |.
              ((bytes.[ sz 1 ] <: u8) >>! 7l <: u8)
              <:
              u8)
          <:
          i32)
    }
    <:
    t_IntVec
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 4)
        (cast ((((bytes.[ sz 3 ] <: u8) &. 1uy <: u8) <<! 4l <: u8) |.
              ((bytes.[ sz 2 ] <: u8) >>! 4l <: u8)
              <:
              u8)
          <:
          i32)
    }
    <:
    t_IntVec
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 5)
        (cast (((bytes.[ sz 3 ] <: u8) >>! 1l <: u8) &. 31uy <: u8) <: i32)
    }
    <:
    t_IntVec
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 6)
        (cast ((((bytes.[ sz 4 ] <: u8) &. 7uy <: u8) <<! 2l <: u8) |.
              ((bytes.[ sz 3 ] <: u8) >>! 6l <: u8)
              <:
              u8)
          <:
          i32)
    }
    <:
    t_IntVec
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 7)
        (cast ((bytes.[ sz 4 ] <: u8) >>! 3l <: u8) <: i32)
    }
    <:
    t_IntVec
  in
  a

let int_vec_from_i32_array (a: t_Array i32 (sz 8)) = { f_elements = a } <: t_IntVec

let int_vec_to_i32_array (a: t_IntVec) = a.f_elements

let inv_ntt_layer_1_int_vec_step (a: t_IntVec) (zeta1 zeta2: i32) =
  let a_minus_b:i32 = (a.f_elements.[ sz 2 ] <: i32) -! (a.f_elements.[ sz 0 ] <: i32) in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 0)
        ((a.f_elements.[ sz 0 ] <: i32) +! (a.f_elements.[ sz 2 ] <: i32) <: i32)
    }
    <:
    t_IntVec
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 2)
        (Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta1 <: i32)
    }
    <:
    t_IntVec
  in
  let a_minus_b:i32 = (a.f_elements.[ sz 3 ] <: i32) -! (a.f_elements.[ sz 1 ] <: i32) in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 1)
        ((a.f_elements.[ sz 1 ] <: i32) +! (a.f_elements.[ sz 3 ] <: i32) <: i32)
    }
    <:
    t_IntVec
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 3)
        (Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta1 <: i32)
    }
    <:
    t_IntVec
  in
  let a_minus_b:i32 = (a.f_elements.[ sz 6 ] <: i32) -! (a.f_elements.[ sz 4 ] <: i32) in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 4)
        ((a.f_elements.[ sz 4 ] <: i32) +! (a.f_elements.[ sz 6 ] <: i32) <: i32)
    }
    <:
    t_IntVec
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 6)
        (Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta2 <: i32)
    }
    <:
    t_IntVec
  in
  let a_minus_b:i32 = (a.f_elements.[ sz 7 ] <: i32) -! (a.f_elements.[ sz 5 ] <: i32) in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 5)
        ((a.f_elements.[ sz 5 ] <: i32) +! (a.f_elements.[ sz 7 ] <: i32) <: i32)
    }
    <:
    t_IntVec
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 7)
        (Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta2 <: i32)
    }
    <:
    t_IntVec
  in
  a

let inv_ntt_layer_2_int_vec_step (a: t_IntVec) (zeta: i32) =
  let a_minus_b:i32 = (a.f_elements.[ sz 4 ] <: i32) -! (a.f_elements.[ sz 0 ] <: i32) in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 0)
        ((a.f_elements.[ sz 0 ] <: i32) +! (a.f_elements.[ sz 4 ] <: i32) <: i32)
    }
    <:
    t_IntVec
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 4)
        (Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta <: i32)
    }
    <:
    t_IntVec
  in
  let a_minus_b:i32 = (a.f_elements.[ sz 5 ] <: i32) -! (a.f_elements.[ sz 1 ] <: i32) in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 1)
        ((a.f_elements.[ sz 1 ] <: i32) +! (a.f_elements.[ sz 5 ] <: i32) <: i32)
    }
    <:
    t_IntVec
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 5)
        (Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta <: i32)
    }
    <:
    t_IntVec
  in
  let a_minus_b:i32 = (a.f_elements.[ sz 6 ] <: i32) -! (a.f_elements.[ sz 2 ] <: i32) in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 2)
        ((a.f_elements.[ sz 2 ] <: i32) +! (a.f_elements.[ sz 6 ] <: i32) <: i32)
    }
    <:
    t_IntVec
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 6)
        (Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta <: i32)
    }
    <:
    t_IntVec
  in
  let a_minus_b:i32 = (a.f_elements.[ sz 7 ] <: i32) -! (a.f_elements.[ sz 3 ] <: i32) in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 3)
        ((a.f_elements.[ sz 3 ] <: i32) +! (a.f_elements.[ sz 7 ] <: i32) <: i32)
    }
    <:
    t_IntVec
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 7)
        (Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta <: i32)
    }
    <:
    t_IntVec
  in
  a

let left_shift_int_vec (lhs: t_IntVec) (rhs: u8) =
  let lhs:t_IntVec =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_SIZE_VEC
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      lhs
      (fun lhs i ->
          let lhs:t_IntVec = lhs in
          let i:usize = i in
          {
            lhs with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize lhs.f_elements
              i
              ((lhs.f_elements.[ i ] <: i32) <<! rhs <: i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          t_IntVec)
  in
  lhs

let modulus_int_vec_constant_var_time (lhs: t_IntVec) (rhs: i32) =
  let lhs:t_IntVec =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_SIZE_VEC
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      lhs
      (fun lhs i ->
          let lhs:t_IntVec = lhs in
          let i:usize = i in
          {
            lhs with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize lhs.f_elements
              i
              ((lhs.f_elements.[ i ] <: i32) %! rhs <: i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          t_IntVec)
  in
  lhs

let montgomery_reduce_int_vec (a: t_IntVec) =
  let a:t_IntVec =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_SIZE_VEC
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      a
      (fun a i ->
          let a:t_IntVec = a in
          let i:usize = i in
          {
            a with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
              i
              (Libcrux_ml_kem.Arithmetic.montgomery_reduce (a.f_elements.[ i ] <: i32) <: i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          t_IntVec)
  in
  a

let mul_int_vec_constant (lhs: t_IntVec) (rhs: i32) =
  let lhs:t_IntVec =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_SIZE_VEC
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      lhs
      (fun lhs i ->
          let lhs:t_IntVec = lhs in
          let i:usize = i in
          {
            lhs with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize lhs.f_elements
              i
              ((lhs.f_elements.[ i ] <: i32) *! rhs <: i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          t_IntVec)
  in
  lhs

let ntt_layer_1_int_vec_step (a: t_IntVec) (zeta1 zeta2: i32) =
  let t:i32 =
    Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer (a.f_elements.[ sz 2 ] <: i32) zeta1
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 2)
        ((a.f_elements.[ sz 0 ] <: i32) -! t <: i32)
    }
    <:
    t_IntVec
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 0)
        ((a.f_elements.[ sz 0 ] <: i32) +! t <: i32)
    }
    <:
    t_IntVec
  in
  let t:i32 =
    Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer (a.f_elements.[ sz 3 ] <: i32) zeta1
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 3)
        ((a.f_elements.[ sz 1 ] <: i32) -! t <: i32)
    }
    <:
    t_IntVec
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 1)
        ((a.f_elements.[ sz 1 ] <: i32) +! t <: i32)
    }
    <:
    t_IntVec
  in
  let t:i32 =
    Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer (a.f_elements.[ sz 6 ] <: i32) zeta2
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 6)
        ((a.f_elements.[ sz 4 ] <: i32) -! t <: i32)
    }
    <:
    t_IntVec
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 4)
        ((a.f_elements.[ sz 4 ] <: i32) +! t <: i32)
    }
    <:
    t_IntVec
  in
  let t:i32 =
    Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer (a.f_elements.[ sz 7 ] <: i32) zeta2
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 7)
        ((a.f_elements.[ sz 5 ] <: i32) -! t <: i32)
    }
    <:
    t_IntVec
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 5)
        ((a.f_elements.[ sz 5 ] <: i32) +! t <: i32)
    }
    <:
    t_IntVec
  in
  a

let ntt_layer_2_int_vec_step (a: t_IntVec) (zeta: i32) =
  let t:i32 =
    Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer (a.f_elements.[ sz 4 ] <: i32) zeta
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 4)
        ((a.f_elements.[ sz 0 ] <: i32) -! t <: i32)
    }
    <:
    t_IntVec
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 0)
        ((a.f_elements.[ sz 0 ] <: i32) +! t <: i32)
    }
    <:
    t_IntVec
  in
  let t:i32 =
    Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer (a.f_elements.[ sz 5 ] <: i32) zeta
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 5)
        ((a.f_elements.[ sz 1 ] <: i32) -! t <: i32)
    }
    <:
    t_IntVec
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 1)
        ((a.f_elements.[ sz 1 ] <: i32) +! t <: i32)
    }
    <:
    t_IntVec
  in
  let t:i32 =
    Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer (a.f_elements.[ sz 6 ] <: i32) zeta
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 6)
        ((a.f_elements.[ sz 2 ] <: i32) -! t <: i32)
    }
    <:
    t_IntVec
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 2)
        ((a.f_elements.[ sz 2 ] <: i32) +! t <: i32)
    }
    <:
    t_IntVec
  in
  let t:i32 =
    Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer (a.f_elements.[ sz 7 ] <: i32) zeta
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 7)
        ((a.f_elements.[ sz 3 ] <: i32) -! t <: i32)
    }
    <:
    t_IntVec
  in
  let a:t_IntVec =
    {
      a with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a.f_elements
        (sz 3)
        ((a.f_elements.[ sz 3 ] <: i32) +! t <: i32)
    }
    <:
    t_IntVec
  in
  a

let ntt_multiply_int_vec (lhs rhs: t_IntVec) (zeta0 zeta1: i32) =
  let out:t_IntVec = v_ZERO_VEC in
  let product:(i32 & i32) =
    Libcrux_ml_kem.Arithmetic.ntt_multiply_binomials ((lhs.f_elements.[ sz 0 ] <: i32),
        (lhs.f_elements.[ sz 1 ] <: i32)
        <:
        (i32 & i32))
      ((rhs.f_elements.[ sz 0 ] <: i32), (rhs.f_elements.[ sz 1 ] <: i32) <: (i32 & i32))
      zeta0
  in
  let out:t_IntVec =
    {
      out with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements (sz 0) product._1
    }
    <:
    t_IntVec
  in
  let out:t_IntVec =
    {
      out with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements (sz 1) product._2
    }
    <:
    t_IntVec
  in
  let product:(i32 & i32) =
    Libcrux_ml_kem.Arithmetic.ntt_multiply_binomials ((lhs.f_elements.[ sz 2 ] <: i32),
        (lhs.f_elements.[ sz 3 ] <: i32)
        <:
        (i32 & i32))
      ((rhs.f_elements.[ sz 2 ] <: i32), (rhs.f_elements.[ sz 3 ] <: i32) <: (i32 & i32))
      (Core.Ops.Arith.Neg.neg zeta0 <: i32)
  in
  let out:t_IntVec =
    {
      out with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements (sz 2) product._1
    }
    <:
    t_IntVec
  in
  let out:t_IntVec =
    {
      out with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements (sz 3) product._2
    }
    <:
    t_IntVec
  in
  let product:(i32 & i32) =
    Libcrux_ml_kem.Arithmetic.ntt_multiply_binomials ((lhs.f_elements.[ sz 4 ] <: i32),
        (lhs.f_elements.[ sz 5 ] <: i32)
        <:
        (i32 & i32))
      ((rhs.f_elements.[ sz 4 ] <: i32), (rhs.f_elements.[ sz 5 ] <: i32) <: (i32 & i32))
      zeta1
  in
  let out:t_IntVec =
    {
      out with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements (sz 4) product._1
    }
    <:
    t_IntVec
  in
  let out:t_IntVec =
    {
      out with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements (sz 5) product._2
    }
    <:
    t_IntVec
  in
  let product:(i32 & i32) =
    Libcrux_ml_kem.Arithmetic.ntt_multiply_binomials ((lhs.f_elements.[ sz 6 ] <: i32),
        (lhs.f_elements.[ sz 7 ] <: i32)
        <:
        (i32 & i32))
      ((rhs.f_elements.[ sz 6 ] <: i32), (rhs.f_elements.[ sz 7 ] <: i32) <: (i32 & i32))
      (Core.Ops.Arith.Neg.neg zeta1 <: i32)
  in
  let out:t_IntVec =
    {
      out with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements (sz 6) product._1
    }
    <:
    t_IntVec
  in
  let out:t_IntVec =
    {
      out with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements (sz 7) product._2
    }
    <:
    t_IntVec
  in
  out

let right_shift_int_vec (lhs: t_IntVec) (rhs: u8) =
  let lhs:t_IntVec =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_SIZE_VEC
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      lhs
      (fun lhs i ->
          let lhs:t_IntVec = lhs in
          let i:usize = i in
          {
            lhs with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize lhs.f_elements
              i
              ((lhs.f_elements.[ i ] <: i32) >>! rhs <: i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          t_IntVec)
  in
  lhs

let serialize_10_int_vec (a: t_IntVec) =
  let result:t_Array u8 (sz 10) = Rust_primitives.Hax.repeat 0uy (sz 10) in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 0)
      (cast ((a.f_elements.[ sz 0 ] <: i32) &. 255l <: i32) <: u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 1)
      (((cast ((a.f_elements.[ sz 1 ] <: i32) &. 63l <: i32) <: u8) <<! 2l <: u8) |.
        (cast (((a.f_elements.[ sz 0 ] <: i32) >>! 8l <: i32) &. 3l <: i32) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 2)
      (((cast ((a.f_elements.[ sz 2 ] <: i32) &. 15l <: i32) <: u8) <<! 4l <: u8) |.
        (cast (((a.f_elements.[ sz 1 ] <: i32) >>! 6l <: i32) &. 15l <: i32) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 3)
      (((cast ((a.f_elements.[ sz 3 ] <: i32) &. 3l <: i32) <: u8) <<! 6l <: u8) |.
        (cast (((a.f_elements.[ sz 2 ] <: i32) >>! 4l <: i32) &. 63l <: i32) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 4)
      (cast (((a.f_elements.[ sz 3 ] <: i32) >>! 2l <: i32) &. 255l <: i32) <: u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 5)
      (cast ((a.f_elements.[ sz 4 ] <: i32) &. 255l <: i32) <: u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 6)
      (((cast ((a.f_elements.[ sz 5 ] <: i32) &. 63l <: i32) <: u8) <<! 2l <: u8) |.
        (cast (((a.f_elements.[ sz 4 ] <: i32) >>! 8l <: i32) &. 3l <: i32) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 7)
      (((cast ((a.f_elements.[ sz 6 ] <: i32) &. 15l <: i32) <: u8) <<! 4l <: u8) |.
        (cast (((a.f_elements.[ sz 5 ] <: i32) >>! 6l <: i32) &. 15l <: i32) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 8)
      (((cast ((a.f_elements.[ sz 7 ] <: i32) &. 3l <: i32) <: u8) <<! 6l <: u8) |.
        (cast (((a.f_elements.[ sz 6 ] <: i32) >>! 4l <: i32) &. 63l <: i32) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 9)
      (cast (((a.f_elements.[ sz 7 ] <: i32) >>! 2l <: i32) &. 255l <: i32) <: u8)
  in
  result

let serialize_11_int_vec (a: t_IntVec) =
  let result:t_Array u8 (sz 11) = Rust_primitives.Hax.repeat 0uy (sz 11) in
  let result:t_Array u8 (sz 11) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 0)
      (cast (a.f_elements.[ sz 0 ] <: i32) <: u8)
  in
  let result:t_Array u8 (sz 11) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 1)
      (((cast ((a.f_elements.[ sz 1 ] <: i32) &. 31l <: i32) <: u8) <<! 3l <: u8) |.
        (cast ((a.f_elements.[ sz 0 ] <: i32) >>! 8l <: i32) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 11) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 2)
      (((cast ((a.f_elements.[ sz 2 ] <: i32) &. 3l <: i32) <: u8) <<! 6l <: u8) |.
        (cast ((a.f_elements.[ sz 1 ] <: i32) >>! 5l <: i32) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 11) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 3)
      (cast (((a.f_elements.[ sz 2 ] <: i32) >>! 2l <: i32) &. 255l <: i32) <: u8)
  in
  let result:t_Array u8 (sz 11) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 4)
      (((cast ((a.f_elements.[ sz 3 ] <: i32) &. 127l <: i32) <: u8) <<! 1l <: u8) |.
        (cast ((a.f_elements.[ sz 2 ] <: i32) >>! 10l <: i32) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 11) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 5)
      (((cast ((a.f_elements.[ sz 4 ] <: i32) &. 15l <: i32) <: u8) <<! 4l <: u8) |.
        (cast ((a.f_elements.[ sz 3 ] <: i32) >>! 7l <: i32) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 11) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 6)
      (((cast ((a.f_elements.[ sz 5 ] <: i32) &. 1l <: i32) <: u8) <<! 7l <: u8) |.
        (cast ((a.f_elements.[ sz 4 ] <: i32) >>! 4l <: i32) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 11) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 7)
      (cast (((a.f_elements.[ sz 5 ] <: i32) >>! 1l <: i32) &. 255l <: i32) <: u8)
  in
  let result:t_Array u8 (sz 11) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 8)
      (((cast ((a.f_elements.[ sz 6 ] <: i32) &. 63l <: i32) <: u8) <<! 2l <: u8) |.
        (cast ((a.f_elements.[ sz 5 ] <: i32) >>! 9l <: i32) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 11) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 9)
      (((cast ((a.f_elements.[ sz 7 ] <: i32) &. 7l <: i32) <: u8) <<! 5l <: u8) |.
        (cast ((a.f_elements.[ sz 6 ] <: i32) >>! 6l <: i32) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 11) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 10)
      (cast ((a.f_elements.[ sz 7 ] <: i32) >>! 3l <: i32) <: u8)
  in
  result

let serialize_12_int_vec (a: t_IntVec) =
  let result:t_Array u8 (sz 12) = Rust_primitives.Hax.repeat 0uy (sz 12) in
  let result:t_Array u8 (sz 12) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 0)
      (cast ((a.f_elements.[ sz 0 ] <: i32) &. 255l <: i32) <: u8)
  in
  let result:t_Array u8 (sz 12) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 1)
      (cast (((a.f_elements.[ sz 0 ] <: i32) >>! 8l <: i32) |.
            (((a.f_elements.[ sz 1 ] <: i32) &. 15l <: i32) <<! 4l <: i32)
            <:
            i32)
        <:
        u8)
  in
  let result:t_Array u8 (sz 12) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 2)
      (cast (((a.f_elements.[ sz 1 ] <: i32) >>! 4l <: i32) &. 255l <: i32) <: u8)
  in
  let result:t_Array u8 (sz 12) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 3)
      (cast ((a.f_elements.[ sz 2 ] <: i32) &. 255l <: i32) <: u8)
  in
  let result:t_Array u8 (sz 12) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 4)
      (cast (((a.f_elements.[ sz 2 ] <: i32) >>! 8l <: i32) |.
            (((a.f_elements.[ sz 3 ] <: i32) &. 15l <: i32) <<! 4l <: i32)
            <:
            i32)
        <:
        u8)
  in
  let result:t_Array u8 (sz 12) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 5)
      (cast (((a.f_elements.[ sz 3 ] <: i32) >>! 4l <: i32) &. 255l <: i32) <: u8)
  in
  let result:t_Array u8 (sz 12) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 6)
      (cast ((a.f_elements.[ sz 4 ] <: i32) &. 255l <: i32) <: u8)
  in
  let result:t_Array u8 (sz 12) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 7)
      (cast (((a.f_elements.[ sz 4 ] <: i32) >>! 8l <: i32) |.
            (((a.f_elements.[ sz 5 ] <: i32) &. 15l <: i32) <<! 4l <: i32)
            <:
            i32)
        <:
        u8)
  in
  let result:t_Array u8 (sz 12) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 8)
      (cast (((a.f_elements.[ sz 5 ] <: i32) >>! 4l <: i32) &. 255l <: i32) <: u8)
  in
  let result:t_Array u8 (sz 12) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 9)
      (cast ((a.f_elements.[ sz 6 ] <: i32) &. 255l <: i32) <: u8)
  in
  let result:t_Array u8 (sz 12) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 10)
      (cast (((a.f_elements.[ sz 6 ] <: i32) >>! 8l <: i32) |.
            (((a.f_elements.[ sz 7 ] <: i32) &. 15l <: i32) <<! 4l <: i32)
            <:
            i32)
        <:
        u8)
  in
  let result:t_Array u8 (sz 12) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 11)
      (cast (((a.f_elements.[ sz 7 ] <: i32) >>! 4l <: i32) &. 255l <: i32) <: u8)
  in
  result

let serialize_1_int_vec (a: t_IntVec) =
  let result:u8 = 0uy in
  let result:u8 =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_SIZE_VEC
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      result
      (fun result i ->
          let result:u8 = result in
          let i:usize = i in
          result |. ((cast (a.f_elements.[ i ] <: i32) <: u8) <<! i <: u8) <: u8)
  in
  result

let serialize_4_int_vec (a: t_IntVec) =
  let result:t_Array u8 (sz 4) = Rust_primitives.Hax.repeat 0uy (sz 4) in
  let result:t_Array u8 (sz 4) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 0)
      (((cast (a.f_elements.[ sz 1 ] <: i32) <: u8) <<! 4l <: u8) |.
        (cast (a.f_elements.[ sz 0 ] <: i32) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 4) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 1)
      (((cast (a.f_elements.[ sz 3 ] <: i32) <: u8) <<! 4l <: u8) |.
        (cast (a.f_elements.[ sz 2 ] <: i32) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 4) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 2)
      (((cast (a.f_elements.[ sz 5 ] <: i32) <: u8) <<! 4l <: u8) |.
        (cast (a.f_elements.[ sz 4 ] <: i32) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 4) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 3)
      (((cast (a.f_elements.[ sz 7 ] <: i32) <: u8) <<! 4l <: u8) |.
        (cast (a.f_elements.[ sz 6 ] <: i32) <: u8)
        <:
        u8)
  in
  result

let serialize_5_int_vec (a: t_IntVec) =
  let result:t_Array u8 (sz 5) = Rust_primitives.Hax.repeat 0uy (sz 5) in
  let result:t_Array u8 (sz 5) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 0)
      (cast ((((a.f_elements.[ sz 1 ] <: i32) &. 7l <: i32) <<! 5l <: i32) |.
            (a.f_elements.[ sz 0 ] <: i32)
            <:
            i32)
        <:
        u8)
  in
  let result:t_Array u8 (sz 5) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 1)
      (cast (((((a.f_elements.[ sz 3 ] <: i32) &. 1l <: i32) <<! 7l <: i32) |.
              ((a.f_elements.[ sz 2 ] <: i32) <<! 2l <: i32)
              <:
              i32) |.
            ((a.f_elements.[ sz 1 ] <: i32) >>! 3l <: i32)
            <:
            i32)
        <:
        u8)
  in
  let result:t_Array u8 (sz 5) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 2)
      (cast ((((a.f_elements.[ sz 4 ] <: i32) &. 15l <: i32) <<! 4l <: i32) |.
            ((a.f_elements.[ sz 3 ] <: i32) >>! 1l <: i32)
            <:
            i32)
        <:
        u8)
  in
  let result:t_Array u8 (sz 5) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 3)
      (cast (((((a.f_elements.[ sz 6 ] <: i32) &. 3l <: i32) <<! 6l <: i32) |.
              ((a.f_elements.[ sz 5 ] <: i32) <<! 1l <: i32)
              <:
              i32) |.
            ((a.f_elements.[ sz 4 ] <: i32) >>! 4l <: i32)
            <:
            i32)
        <:
        u8)
  in
  let result:t_Array u8 (sz 5) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 4)
      (cast (((a.f_elements.[ sz 7 ] <: i32) <<! 3l <: i32) |.
            ((a.f_elements.[ sz 6 ] <: i32) >>! 2l <: i32)
            <:
            i32)
        <:
        u8)
  in
  result

let sub_int_vec (lhs rhs: t_IntVec) =
  let lhs:t_IntVec =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_SIZE_VEC
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      lhs
      (fun lhs i ->
          let lhs:t_IntVec = lhs in
          let i:usize = i in
          {
            lhs with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize lhs.f_elements
              i
              ((lhs.f_elements.[ i ] <: i32) -! (rhs.f_elements.[ i ] <: i32) <: i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          t_IntVec)
  in
  lhs
