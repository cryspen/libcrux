module Libcrux_ml_kem.Vector.Portable.Serialize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let serialize_1_ (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  let result:t_Array u8 (sz 2) = Rust_primitives.Hax.repeat 0uy (sz 2) in
  let result:t_Array u8 (sz 2) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          #FStar.Tactics.Typeclasses.solve
          ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 8 }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
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
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          #FStar.Tactics.Typeclasses.solve
          ({ Core.Ops.Range.f_start = sz 8; Core.Ops.Range.f_end = sz 16 }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
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
  let result:t_Array u8 (sz 20) = Rust_primitives.Hax.repeat 0uy (sz 20) in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 0)
      (cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 0 ] <: i16) &. 255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 1)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 1 ] <: i16) &. 63s
                <:
                i16)
            <:
            u8) <<!
          2l
          <:
          u8) |.
        (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 0 ] <: i16) >>! 8l
                <:
                i16) &.
              3s
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 2)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 2 ] <: i16) &. 15s
                <:
                i16)
            <:
            u8) <<!
          4l
          <:
          u8) |.
        (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 1 ] <: i16) >>! 6l
                <:
                i16) &.
              15s
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 3)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 3 ] <: i16) &. 3s
                <:
                i16)
            <:
            u8) <<!
          6l
          <:
          u8) |.
        (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 2 ] <: i16) >>! 4l
                <:
                i16) &.
              63s
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 4)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 3 ] <: i16) >>! 2l
              <:
              i16) &.
            255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 5)
      (cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 4 ] <: i16) &. 255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 6)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 5 ] <: i16) &. 63s
                <:
                i16)
            <:
            u8) <<!
          2l
          <:
          u8) |.
        (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 4 ] <: i16) >>! 8l
                <:
                i16) &.
              3s
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 7)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 6 ] <: i16) &. 15s
                <:
                i16)
            <:
            u8) <<!
          4l
          <:
          u8) |.
        (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 5 ] <: i16) >>! 6l
                <:
                i16) &.
              15s
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 8)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 7 ] <: i16) &. 3s
                <:
                i16)
            <:
            u8) <<!
          6l
          <:
          u8) |.
        (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 6 ] <: i16) >>! 4l
                <:
                i16) &.
              63s
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 9)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 7 ] <: i16) >>! 2l
              <:
              i16) &.
            255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 10)
      (cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 0 <: usize ]
              <:
              i16) &.
            255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 11)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 1 <: usize ]
                  <:
                  i16) &.
                63s
                <:
                i16)
            <:
            u8) <<!
          2l
          <:
          u8) |.
        (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 0 <: usize ]
                  <:
                  i16) >>!
                8l
                <:
                i16) &.
              3s
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 12)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 2 <: usize ]
                  <:
                  i16) &.
                15s
                <:
                i16)
            <:
            u8) <<!
          4l
          <:
          u8) |.
        (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 1 <: usize ]
                  <:
                  i16) >>!
                6l
                <:
                i16) &.
              15s
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 13)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 3 <: usize ]
                  <:
                  i16) &.
                3s
                <:
                i16)
            <:
            u8) <<!
          6l
          <:
          u8) |.
        (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 2 <: usize ]
                  <:
                  i16) >>!
                4l
                <:
                i16) &.
              63s
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 14)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 3 <: usize ]
                <:
                i16) >>!
              2l
              <:
              i16) &.
            255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 15)
      (cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 4 <: usize ]
              <:
              i16) &.
            255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 16)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 5 <: usize ]
                  <:
                  i16) &.
                63s
                <:
                i16)
            <:
            u8) <<!
          2l
          <:
          u8) |.
        (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 4 <: usize ]
                  <:
                  i16) >>!
                8l
                <:
                i16) &.
              3s
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 17)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 6 <: usize ]
                  <:
                  i16) &.
                15s
                <:
                i16)
            <:
            u8) <<!
          4l
          <:
          u8) |.
        (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 5 <: usize ]
                  <:
                  i16) >>!
                6l
                <:
                i16) &.
              15s
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 18)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 7 <: usize ]
                  <:
                  i16) &.
                3s
                <:
                i16)
            <:
            u8) <<!
          6l
          <:
          u8) |.
        (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 6 <: usize ]
                  <:
                  i16) >>!
                4l
                <:
                i16) &.
              63s
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 19)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 7 <: usize ]
                <:
                i16) >>!
              2l
              <:
              i16) &.
            255s
            <:
            i16)
        <:
        u8)
  in
  result

let serialize_11_ (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  let result:t_Array u8 (sz 22) = Rust_primitives.Hax.repeat 0uy (sz 22) in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 0)
      (cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 0 ] <: i16) <: u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 1)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 1 ] <: i16) &. 31s
                <:
                i16)
            <:
            u8) <<!
          3l
          <:
          u8) |.
        (cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 0 ] <: i16) >>! 8l
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 2)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 2 ] <: i16) &. 3s
                <:
                i16)
            <:
            u8) <<!
          6l
          <:
          u8) |.
        (cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 1 ] <: i16) >>! 5l
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 3)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 2 ] <: i16) >>! 2l
              <:
              i16) &.
            255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 4)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 3 ] <: i16) &. 127s
                <:
                i16)
            <:
            u8) <<!
          1l
          <:
          u8) |.
        (cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 2 ] <: i16) >>! 10l
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 5)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 4 ] <: i16) &. 15s
                <:
                i16)
            <:
            u8) <<!
          4l
          <:
          u8) |.
        (cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 3 ] <: i16) >>! 7l
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 6)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 5 ] <: i16) &. 1s
                <:
                i16)
            <:
            u8) <<!
          7l
          <:
          u8) |.
        (cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 4 ] <: i16) >>! 4l
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 7)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 5 ] <: i16) >>! 1l
              <:
              i16) &.
            255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 8)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 6 ] <: i16) &. 63s
                <:
                i16)
            <:
            u8) <<!
          2l
          <:
          u8) |.
        (cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 5 ] <: i16) >>! 9l
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 9)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 7 ] <: i16) &. 7s
                <:
                i16)
            <:
            u8) <<!
          5l
          <:
          u8) |.
        (cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 6 ] <: i16) >>! 6l
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 10)
      (cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 7 ] <: i16) >>! 3l <: i16
          )
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 11)
      (cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 0 <: usize ]
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 12)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 1 <: usize ]
                  <:
                  i16) &.
                31s
                <:
                i16)
            <:
            u8) <<!
          3l
          <:
          u8) |.
        (cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 0 <: usize ]
                <:
                i16) >>!
              8l
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 13)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 2 <: usize ]
                  <:
                  i16) &.
                3s
                <:
                i16)
            <:
            u8) <<!
          6l
          <:
          u8) |.
        (cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 1 <: usize ]
                <:
                i16) >>!
              5l
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 14)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 2 <: usize ]
                <:
                i16) >>!
              2l
              <:
              i16) &.
            255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 15)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 3 <: usize ]
                  <:
                  i16) &.
                127s
                <:
                i16)
            <:
            u8) <<!
          1l
          <:
          u8) |.
        (cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 2 <: usize ]
                <:
                i16) >>!
              10l
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 16)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 4 <: usize ]
                  <:
                  i16) &.
                15s
                <:
                i16)
            <:
            u8) <<!
          4l
          <:
          u8) |.
        (cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 3 <: usize ]
                <:
                i16) >>!
              7l
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 17)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 5 <: usize ]
                  <:
                  i16) &.
                1s
                <:
                i16)
            <:
            u8) <<!
          7l
          <:
          u8) |.
        (cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 4 <: usize ]
                <:
                i16) >>!
              4l
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 18)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 5 <: usize ]
                <:
                i16) >>!
              1l
              <:
              i16) &.
            255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 19)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 6 <: usize ]
                  <:
                  i16) &.
                63s
                <:
                i16)
            <:
            u8) <<!
          2l
          <:
          u8) |.
        (cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 5 <: usize ]
                <:
                i16) >>!
              9l
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 20)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 7 <: usize ]
                  <:
                  i16) &.
                7s
                <:
                i16)
            <:
            u8) <<!
          5l
          <:
          u8) |.
        (cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 6 <: usize ]
                <:
                i16) >>!
              6l
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 21)
      (cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 7 <: usize ]
              <:
              i16) >>!
            3l
            <:
            i16)
        <:
        u8)
  in
  result

let serialize_12_ (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  let result:t_Array u8 (sz 24) = Rust_primitives.Hax.repeat 0uy (sz 24) in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 0)
      (cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 0 ] <: i16) &. 255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 1)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 0 ] <: i16) >>! 8l
              <:
              i16) |.
            (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 1 ] <: i16) &. 15s
                <:
                i16) <<!
              4l
              <:
              i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 2)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 1 ] <: i16) >>! 4l
              <:
              i16) &.
            255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 3)
      (cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 2 ] <: i16) &. 255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 4)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 2 ] <: i16) >>! 8l
              <:
              i16) |.
            (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 3 ] <: i16) &. 15s
                <:
                i16) <<!
              4l
              <:
              i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 5)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 3 ] <: i16) >>! 4l
              <:
              i16) &.
            255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 6)
      (cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 4 ] <: i16) &. 255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 7)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 4 ] <: i16) >>! 8l
              <:
              i16) |.
            (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 5 ] <: i16) &. 15s
                <:
                i16) <<!
              4l
              <:
              i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 8)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 5 ] <: i16) >>! 4l
              <:
              i16) &.
            255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 9)
      (cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 6 ] <: i16) &. 255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 10)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 6 ] <: i16) >>! 8l
              <:
              i16) |.
            (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 7 ] <: i16) &. 15s
                <:
                i16) <<!
              4l
              <:
              i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 11)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 7 ] <: i16) >>! 4l
              <:
              i16) &.
            255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 12)
      (cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 0 <: usize ]
              <:
              i16) &.
            255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 13)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 0 <: usize ]
                <:
                i16) >>!
              8l
              <:
              i16) |.
            (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 1 <: usize ]
                  <:
                  i16) &.
                15s
                <:
                i16) <<!
              4l
              <:
              i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 14)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 1 <: usize ]
                <:
                i16) >>!
              4l
              <:
              i16) &.
            255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 15)
      (cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 2 <: usize ]
              <:
              i16) &.
            255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 16)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 2 <: usize ]
                <:
                i16) >>!
              8l
              <:
              i16) |.
            (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 3 <: usize ]
                  <:
                  i16) &.
                15s
                <:
                i16) <<!
              4l
              <:
              i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 17)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 3 <: usize ]
                <:
                i16) >>!
              4l
              <:
              i16) &.
            255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 18)
      (cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 4 <: usize ]
              <:
              i16) &.
            255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 19)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 4 <: usize ]
                <:
                i16) >>!
              8l
              <:
              i16) |.
            (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 5 <: usize ]
                  <:
                  i16) &.
                15s
                <:
                i16) <<!
              4l
              <:
              i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 20)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 5 <: usize ]
                <:
                i16) >>!
              4l
              <:
              i16) &.
            255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 21)
      (cast ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 6 <: usize ]
              <:
              i16) &.
            255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 22)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 6 <: usize ]
                <:
                i16) >>!
              8l
              <:
              i16) |.
            (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 7 <: usize ]
                  <:
                  i16) &.
                15s
                <:
                i16) <<!
              4l
              <:
              i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 23)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 7 <: usize ]
                <:
                i16) >>!
              4l
              <:
              i16) &.
            255s
            <:
            i16)
        <:
        u8)
  in
  result

let serialize_4_ (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  let result:t_Array u8 (sz 8) = Rust_primitives.Hax.repeat 0uy (sz 8) in
  let result:t_Array u8 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 0)
      (((cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 1 ] <: i16) <: u8) <<!
          4l
          <:
          u8) |.
        (cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 0 ] <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 1)
      (((cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 3 ] <: i16) <: u8) <<!
          4l
          <:
          u8) |.
        (cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 2 ] <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 2)
      (((cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 5 ] <: i16) <: u8) <<!
          4l
          <:
          u8) |.
        (cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 4 ] <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 3)
      (((cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 7 ] <: i16) <: u8) <<!
          4l
          <:
          u8) |.
        (cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 6 ] <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 4)
      (((cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 1 <: usize ]
                <:
                i16)
            <:
            u8) <<!
          4l
          <:
          u8) |.
        (cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 0 <: usize ]
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 5)
      (((cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 3 <: usize ]
                <:
                i16)
            <:
            u8) <<!
          4l
          <:
          u8) |.
        (cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 2 <: usize ]
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 6)
      (((cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 5 <: usize ]
                <:
                i16)
            <:
            u8) <<!
          4l
          <:
          u8) |.
        (cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 4 <: usize ]
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 7)
      (((cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 7 <: usize ]
                <:
                i16)
            <:
            u8) <<!
          4l
          <:
          u8) |.
        (cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 6 <: usize ]
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  result

let serialize_5_ (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  let result:t_Array u8 (sz 10) = Rust_primitives.Hax.repeat 0uy (sz 10) in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 0)
      (cast ((((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 1 ] <: i16) &. 7s
                <:
                i16) <<!
              5l
              <:
              i16) |.
            (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 0 ] <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 1)
      (cast (((((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 3 ] <: i16) &. 1s
                  <:
                  i16) <<!
                7l
                <:
                i16) |.
              ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 2 ] <: i16) <<! 2l
                <:
                i16)
              <:
              i16) |.
            ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 1 ] <: i16) >>! 3l <: i16
            )
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 2)
      (cast ((((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 4 ] <: i16) &. 15s
                <:
                i16) <<!
              4l
              <:
              i16) |.
            ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 3 ] <: i16) >>! 1l <: i16
            )
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 3)
      (cast (((((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 6 ] <: i16) &. 3s
                  <:
                  i16) <<!
                6l
                <:
                i16) |.
              ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 5 ] <: i16) <<! 1l
                <:
                i16)
              <:
              i16) |.
            ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 4 ] <: i16) >>! 4l <: i16
            )
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 4)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 7 ] <: i16) <<! 3l
              <:
              i16) |.
            ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 6 ] <: i16) >>! 2l <: i16
            )
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 5)
      (cast ((((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 1 <: usize ]
                  <:
                  i16) &.
                7s
                <:
                i16) <<!
              5l
              <:
              i16) |.
            (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 0 <: usize ]
              <:
              i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 6)
      (cast (((((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 3 <: usize ]
                    <:
                    i16) &.
                  1s
                  <:
                  i16) <<!
                7l
                <:
                i16) |.
              ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 2 <: usize ]
                  <:
                  i16) <<!
                2l
                <:
                i16)
              <:
              i16) |.
            ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 1 <: usize ]
                <:
                i16) >>!
              3l
              <:
              i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 7)
      (cast ((((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 4 <: usize ]
                  <:
                  i16) &.
                15s
                <:
                i16) <<!
              4l
              <:
              i16) |.
            ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 3 <: usize ]
                <:
                i16) >>!
              1l
              <:
              i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 8)
      (cast (((((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 6 <: usize ]
                    <:
                    i16) &.
                  3s
                  <:
                  i16) <<!
                6l
                <:
                i16) |.
              ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 5 <: usize ]
                  <:
                  i16) <<!
                1l
                <:
                i16)
              <:
              i16) |.
            ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 4 <: usize ]
                <:
                i16) >>!
              4l
              <:
              i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 9)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 7 <: usize ]
                <:
                i16) <<!
              3l
              <:
              i16) |.
            ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 6 <: usize ]
                <:
                i16) >>!
              2l
              <:
              i16)
            <:
            i16)
        <:
        u8)
  in
  result

let deserialize_1_ (v: t_Slice u8) =
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Libcrux_ml_kem.Vector.Portable.Vector_type.zero ()
  in
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          #FStar.Tactics.Typeclasses.solve
          ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 8 }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
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
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          #FStar.Tactics.Typeclasses.solve
          ({
              Core.Ops.Range.f_start = sz 8;
              Core.Ops.Range.f_end = Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
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
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Libcrux_ml_kem.Vector.Portable.Vector_type.zero ()
  in
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 0)
        ((((cast (bytes.[ sz 1 ] <: u8) <: i16) &. 3s <: i16) <<! 8l <: i16) |.
          ((cast (bytes.[ sz 0 ] <: u8) <: i16) &. 255s <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 1)
        ((((cast (bytes.[ sz 2 ] <: u8) <: i16) &. 15s <: i16) <<! 6l <: i16) |.
          ((cast (bytes.[ sz 1 ] <: u8) <: i16) >>! 2l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 2)
        ((((cast (bytes.[ sz 3 ] <: u8) <: i16) &. 63s <: i16) <<! 4l <: i16) |.
          ((cast (bytes.[ sz 2 ] <: u8) <: i16) >>! 4l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 3)
        (((cast (bytes.[ sz 4 ] <: u8) <: i16) <<! 2l <: i16) |.
          ((cast (bytes.[ sz 3 ] <: u8) <: i16) >>! 6l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 4)
        ((((cast (bytes.[ sz 6 ] <: u8) <: i16) &. 3s <: i16) <<! 8l <: i16) |.
          ((cast (bytes.[ sz 5 ] <: u8) <: i16) &. 255s <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 5)
        ((((cast (bytes.[ sz 7 ] <: u8) <: i16) &. 15s <: i16) <<! 6l <: i16) |.
          ((cast (bytes.[ sz 6 ] <: u8) <: i16) >>! 2l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 6)
        ((((cast (bytes.[ sz 8 ] <: u8) <: i16) &. 63s <: i16) <<! 4l <: i16) |.
          ((cast (bytes.[ sz 7 ] <: u8) <: i16) >>! 4l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 7)
        (((cast (bytes.[ sz 9 ] <: u8) <: i16) <<! 2l <: i16) |.
          ((cast (bytes.[ sz 8 ] <: u8) <: i16) >>! 6l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8)
        ((((cast (bytes.[ sz 10 +! sz 1 <: usize ] <: u8) <: i16) &. 3s <: i16) <<! 8l <: i16) |.
          ((cast (bytes.[ sz 10 +! sz 0 <: usize ] <: u8) <: i16) &. 255s <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 9)
        ((((cast (bytes.[ sz 10 +! sz 2 <: usize ] <: u8) <: i16) &. 15s <: i16) <<! 6l <: i16) |.
          ((cast (bytes.[ sz 10 +! sz 1 <: usize ] <: u8) <: i16) >>! 2l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 10)
        ((((cast (bytes.[ sz 10 +! sz 3 <: usize ] <: u8) <: i16) &. 63s <: i16) <<! 4l <: i16) |.
          ((cast (bytes.[ sz 10 +! sz 2 <: usize ] <: u8) <: i16) >>! 4l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 11)
        (((cast (bytes.[ sz 10 +! sz 4 <: usize ] <: u8) <: i16) <<! 2l <: i16) |.
          ((cast (bytes.[ sz 10 +! sz 3 <: usize ] <: u8) <: i16) >>! 6l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 12)
        ((((cast (bytes.[ sz 10 +! sz 6 <: usize ] <: u8) <: i16) &. 3s <: i16) <<! 8l <: i16) |.
          ((cast (bytes.[ sz 10 +! sz 5 <: usize ] <: u8) <: i16) &. 255s <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 13)
        ((((cast (bytes.[ sz 10 +! sz 7 <: usize ] <: u8) <: i16) &. 15s <: i16) <<! 6l <: i16) |.
          ((cast (bytes.[ sz 10 +! sz 6 <: usize ] <: u8) <: i16) >>! 2l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 14)
        ((((cast (bytes.[ sz 10 +! sz 8 <: usize ] <: u8) <: i16) &. 63s <: i16) <<! 4l <: i16) |.
          ((cast (bytes.[ sz 10 +! sz 7 <: usize ] <: u8) <: i16) >>! 4l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 15)
        (((cast (bytes.[ sz 10 +! sz 9 <: usize ] <: u8) <: i16) <<! 2l <: i16) |.
          ((cast (bytes.[ sz 10 +! sz 8 <: usize ] <: u8) <: i16) >>! 6l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  result

let deserialize_11_ (bytes: t_Slice u8) =
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Libcrux_ml_kem.Vector.Portable.Vector_type.zero ()
  in
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 0)
        ((((cast (bytes.[ sz 1 ] <: u8) <: i16) &. 7s <: i16) <<! 8l <: i16) |.
          (cast (bytes.[ sz 0 ] <: u8) <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 1)
        ((((cast (bytes.[ sz 2 ] <: u8) <: i16) &. 63s <: i16) <<! 5l <: i16) |.
          ((cast (bytes.[ sz 1 ] <: u8) <: i16) >>! 3l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
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
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 3)
        ((((cast (bytes.[ sz 5 ] <: u8) <: i16) &. 15s <: i16) <<! 7l <: i16) |.
          ((cast (bytes.[ sz 4 ] <: u8) <: i16) >>! 1l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 4)
        ((((cast (bytes.[ sz 6 ] <: u8) <: i16) &. 127s <: i16) <<! 4l <: i16) |.
          ((cast (bytes.[ sz 5 ] <: u8) <: i16) >>! 4l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
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
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 6)
        ((((cast (bytes.[ sz 9 ] <: u8) <: i16) &. 31s <: i16) <<! 6l <: i16) |.
          ((cast (bytes.[ sz 8 ] <: u8) <: i16) >>! 2l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 7)
        (((cast (bytes.[ sz 10 ] <: u8) <: i16) <<! 3l <: i16) |.
          ((cast (bytes.[ sz 9 ] <: u8) <: i16) >>! 5l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8)
        ((((cast (bytes.[ sz 11 +! sz 1 <: usize ] <: u8) <: i16) &. 7s <: i16) <<! 8l <: i16) |.
          (cast (bytes.[ sz 11 +! sz 0 <: usize ] <: u8) <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 9)
        ((((cast (bytes.[ sz 11 +! sz 2 <: usize ] <: u8) <: i16) &. 63s <: i16) <<! 5l <: i16) |.
          ((cast (bytes.[ sz 11 +! sz 1 <: usize ] <: u8) <: i16) >>! 3l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
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
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 11)
        ((((cast (bytes.[ sz 11 +! sz 5 <: usize ] <: u8) <: i16) &. 15s <: i16) <<! 7l <: i16) |.
          ((cast (bytes.[ sz 11 +! sz 4 <: usize ] <: u8) <: i16) >>! 1l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 12)
        ((((cast (bytes.[ sz 11 +! sz 6 <: usize ] <: u8) <: i16) &. 127s <: i16) <<! 4l <: i16) |.
          ((cast (bytes.[ sz 11 +! sz 5 <: usize ] <: u8) <: i16) >>! 4l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
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
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 14)
        ((((cast (bytes.[ sz 11 +! sz 9 <: usize ] <: u8) <: i16) &. 31s <: i16) <<! 6l <: i16) |.
          ((cast (bytes.[ sz 11 +! sz 8 <: usize ] <: u8) <: i16) >>! 2l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 15)
        (((cast (bytes.[ sz 11 +! sz 10 <: usize ] <: u8) <: i16) <<! 3l <: i16) |.
          ((cast (bytes.[ sz 11 +! sz 9 <: usize ] <: u8) <: i16) >>! 5l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  result

let deserialize_12_ (bytes: t_Slice u8) =
  let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Libcrux_ml_kem.Vector.Portable.Vector_type.zero ()
  in
  let byte0:i16 = cast (bytes.[ sz 0 ] <: u8) <: i16 in
  let byte1:i16 = cast (bytes.[ sz 1 ] <: u8) <: i16 in
  let byte2:i16 = cast (bytes.[ sz 2 ] <: u8) <: i16 in
  let byte3:i16 = cast (bytes.[ sz 3 ] <: u8) <: i16 in
  let byte4:i16 = cast (bytes.[ sz 4 ] <: u8) <: i16 in
  let byte5:i16 = cast (bytes.[ sz 5 ] <: u8) <: i16 in
  let byte6:i16 = cast (bytes.[ sz 6 ] <: u8) <: i16 in
  let byte7:i16 = cast (bytes.[ sz 7 ] <: u8) <: i16 in
  let byte8:i16 = cast (bytes.[ sz 8 ] <: u8) <: i16 in
  let byte9:i16 = cast (bytes.[ sz 9 ] <: u8) <: i16 in
  let byte10:i16 = cast (bytes.[ sz 10 ] <: u8) <: i16 in
  let byte11:i16 = cast (bytes.[ sz 11 ] <: u8) <: i16 in
  let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      re with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 0)
        (((byte1 &. 15s <: i16) <<! 8l <: i16) |. (byte0 &. 255s <: i16) <: i16)
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
        ((byte2 <<! 4l <: i16) |. ((byte1 >>! 4l <: i16) &. 15s <: i16) <: i16)
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
        (((byte4 &. 15s <: i16) <<! 8l <: i16) |. (byte3 &. 255s <: i16) <: i16)
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
        ((byte5 <<! 4l <: i16) |. ((byte4 >>! 4l <: i16) &. 15s <: i16) <: i16)
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
        (((byte7 &. 15s <: i16) <<! 8l <: i16) |. (byte6 &. 255s <: i16) <: i16)
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
        ((byte8 <<! 4l <: i16) |. ((byte7 >>! 4l <: i16) &. 15s <: i16) <: i16)
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
        (((byte10 &. 15s <: i16) <<! 8l <: i16) |. (byte9 &. 255s <: i16) <: i16)
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
        ((byte11 <<! 4l <: i16) |. ((byte10 >>! 4l <: i16) &. 15s <: i16) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let byte12:i16 = cast (bytes.[ sz 12 ] <: u8) <: i16 in
  let byte13:i16 = cast (bytes.[ sz 13 ] <: u8) <: i16 in
  let byte14:i16 = cast (bytes.[ sz 14 ] <: u8) <: i16 in
  let byte15:i16 = cast (bytes.[ sz 15 ] <: u8) <: i16 in
  let byte16:i16 = cast (bytes.[ sz 16 ] <: u8) <: i16 in
  let byte17:i16 = cast (bytes.[ sz 17 ] <: u8) <: i16 in
  let byte18:i16 = cast (bytes.[ sz 18 ] <: u8) <: i16 in
  let byte19:i16 = cast (bytes.[ sz 19 ] <: u8) <: i16 in
  let byte20:i16 = cast (bytes.[ sz 20 ] <: u8) <: i16 in
  let byte21:i16 = cast (bytes.[ sz 21 ] <: u8) <: i16 in
  let byte22:i16 = cast (bytes.[ sz 22 ] <: u8) <: i16 in
  let byte23:i16 = cast (bytes.[ sz 23 ] <: u8) <: i16 in
  let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      re with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8)
        (((byte13 &. 15s <: i16) <<! 8l <: i16) |. (byte12 &. 255s <: i16) <: i16)
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
        ((byte14 <<! 4l <: i16) |. ((byte13 >>! 4l <: i16) &. 15s <: i16) <: i16)
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
        (((byte16 &. 15s <: i16) <<! 8l <: i16) |. (byte15 &. 255s <: i16) <: i16)
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
        ((byte17 <<! 4l <: i16) |. ((byte16 >>! 4l <: i16) &. 15s <: i16) <: i16)
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
        (((byte19 &. 15s <: i16) <<! 8l <: i16) |. (byte18 &. 255s <: i16) <: i16)
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
        ((byte20 <<! 4l <: i16) |. ((byte19 >>! 4l <: i16) &. 15s <: i16) <: i16)
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
        (((byte22 &. 15s <: i16) <<! 8l <: i16) |. (byte21 &. 255s <: i16) <: i16)
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
        ((byte23 <<! 4l <: i16) |. ((byte22 >>! 4l <: i16) &. 15s <: i16) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  re

let deserialize_4_ (bytes: t_Slice u8) =
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
        (cast ((bytes.[ sz 0 ] <: u8) &. 15uy <: u8) <: i16)
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
        (cast (((bytes.[ sz 0 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i16)
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
        (cast ((bytes.[ sz 1 ] <: u8) &. 15uy <: u8) <: i16)
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
        (cast (((bytes.[ sz 1 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i16)
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
        (cast ((bytes.[ sz 2 ] <: u8) &. 15uy <: u8) <: i16)
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
        (cast (((bytes.[ sz 2 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i16)
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
        (cast ((bytes.[ sz 3 ] <: u8) &. 15uy <: u8) <: i16)
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
        (cast (((bytes.[ sz 3 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i16)
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
        (cast ((bytes.[ sz 4 ] <: u8) &. 15uy <: u8) <: i16)
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
        (cast (((bytes.[ sz 4 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i16)
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
        (cast ((bytes.[ sz 5 ] <: u8) &. 15uy <: u8) <: i16)
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
        (cast (((bytes.[ sz 5 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i16)
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
        (cast ((bytes.[ sz 6 ] <: u8) &. 15uy <: u8) <: i16)
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
        (cast (((bytes.[ sz 6 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i16)
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
        (cast ((bytes.[ sz 7 ] <: u8) &. 15uy <: u8) <: i16)
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
        (cast (((bytes.[ sz 7 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  v

let deserialize_5_ (bytes: t_Slice u8) =
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
        (cast ((bytes.[ sz 0 ] <: u8) &. 31uy <: u8) <: i16)
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
        (cast ((((bytes.[ sz 1 ] <: u8) &. 3uy <: u8) <<! 3l <: u8) |.
              ((bytes.[ sz 0 ] <: u8) >>! 5l <: u8)
              <:
              u8)
          <:
          i16)
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
        (cast (((bytes.[ sz 1 ] <: u8) >>! 2l <: u8) &. 31uy <: u8) <: i16)
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
        (cast ((((bytes.[ sz 2 ] <: u8) &. 15uy <: u8) <<! 1l <: u8) |.
              ((bytes.[ sz 1 ] <: u8) >>! 7l <: u8)
              <:
              u8)
          <:
          i16)
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
        (cast ((((bytes.[ sz 3 ] <: u8) &. 1uy <: u8) <<! 4l <: u8) |.
              ((bytes.[ sz 2 ] <: u8) >>! 4l <: u8)
              <:
              u8)
          <:
          i16)
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
        (cast (((bytes.[ sz 3 ] <: u8) >>! 1l <: u8) &. 31uy <: u8) <: i16)
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
        (cast ((((bytes.[ sz 4 ] <: u8) &. 7uy <: u8) <<! 2l <: u8) |.
              ((bytes.[ sz 3 ] <: u8) >>! 6l <: u8)
              <:
              u8)
          <:
          i16)
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
        (cast ((bytes.[ sz 4 ] <: u8) >>! 3l <: u8) <: i16)
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
        (cast ((bytes.[ sz 5 +! sz 0 <: usize ] <: u8) &. 31uy <: u8) <: i16)
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
        (cast ((((bytes.[ sz 5 +! sz 1 <: usize ] <: u8) &. 3uy <: u8) <<! 3l <: u8) |.
              ((bytes.[ sz 5 +! sz 0 <: usize ] <: u8) >>! 5l <: u8)
              <:
              u8)
          <:
          i16)
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
        (cast (((bytes.[ sz 5 +! sz 1 <: usize ] <: u8) >>! 2l <: u8) &. 31uy <: u8) <: i16)
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
        (cast ((((bytes.[ sz 5 +! sz 2 <: usize ] <: u8) &. 15uy <: u8) <<! 1l <: u8) |.
              ((bytes.[ sz 5 +! sz 1 <: usize ] <: u8) >>! 7l <: u8)
              <:
              u8)
          <:
          i16)
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
        (cast ((((bytes.[ sz 5 +! sz 3 <: usize ] <: u8) &. 1uy <: u8) <<! 4l <: u8) |.
              ((bytes.[ sz 5 +! sz 2 <: usize ] <: u8) >>! 4l <: u8)
              <:
              u8)
          <:
          i16)
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
        (cast (((bytes.[ sz 5 +! sz 3 <: usize ] <: u8) >>! 1l <: u8) &. 31uy <: u8) <: i16)
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
        (cast ((((bytes.[ sz 5 +! sz 4 <: usize ] <: u8) &. 7uy <: u8) <<! 2l <: u8) |.
              ((bytes.[ sz 5 +! sz 3 <: usize ] <: u8) >>! 6l <: u8)
              <:
              u8)
          <:
          i16)
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
        (cast ((bytes.[ sz 5 +! sz 4 <: usize ] <: u8) >>! 3l <: u8) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  v
