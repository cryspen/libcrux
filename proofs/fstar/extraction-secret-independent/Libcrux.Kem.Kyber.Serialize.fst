module Libcrux.Kem.Kyber.Serialize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let compress_coefficients_10_ (coefficient1 coefficient2 coefficient3 coefficient4: i32) =
  let coef1:u8 = cast (coefficient1 &. 255l <: i32) <: u8 in
  let coef2:u8 =
    ((cast (coefficient2 &. 63l <: i32) <: u8) <<! 2l <: u8) |.
    (cast ((coefficient1 >>! 8l <: i32) &. 3l <: i32) <: u8)
  in
  let coef3:u8 =
    ((cast (coefficient3 &. 15l <: i32) <: u8) <<! 4l <: u8) |.
    (cast ((coefficient2 >>! 6l <: i32) &. 15l <: i32) <: u8)
  in
  let coef4:u8 =
    ((cast (coefficient4 &. 3l <: i32) <: u8) <<! 6l <: u8) |.
    (cast ((coefficient3 >>! 4l <: i32) &. 63l <: i32) <: u8)
  in
  let coef5:u8 = cast ((coefficient4 >>! 2l <: i32) &. 255l <: i32) <: u8 in
  coef1, coef2, coef3, coef4, coef5 <: (u8 & u8 & u8 & u8 & u8)

let compress_coefficients_11_
      (coefficient1 coefficient2 coefficient3 coefficient4 coefficient5 coefficient6 coefficient7 coefficient8:
          i32)
     =
  let coef1:u8 = cast (coefficient1 <: i32) <: u8 in
  let coef2:u8 =
    ((cast (coefficient2 &. 31l <: i32) <: u8) <<! 3l <: u8) |.
    (cast (coefficient1 >>! 8l <: i32) <: u8)
  in
  let coef3:u8 =
    ((cast (coefficient3 &. 3l <: i32) <: u8) <<! 6l <: u8) |.
    (cast (coefficient2 >>! 5l <: i32) <: u8)
  in
  let coef4:u8 = cast ((coefficient3 >>! 2l <: i32) &. 255l <: i32) <: u8 in
  let coef5:u8 =
    ((cast (coefficient4 &. 127l <: i32) <: u8) <<! 1l <: u8) |.
    (cast (coefficient3 >>! 10l <: i32) <: u8)
  in
  let coef6:u8 =
    ((cast (coefficient5 &. 15l <: i32) <: u8) <<! 4l <: u8) |.
    (cast (coefficient4 >>! 7l <: i32) <: u8)
  in
  let coef7:u8 =
    ((cast (coefficient6 &. 1l <: i32) <: u8) <<! 7l <: u8) |.
    (cast (coefficient5 >>! 4l <: i32) <: u8)
  in
  let coef8:u8 = cast ((coefficient6 >>! 1l <: i32) &. 255l <: i32) <: u8 in
  let coef9:u8 =
    ((cast (coefficient7 &. 63l <: i32) <: u8) <<! 2l <: u8) |.
    (cast (coefficient6 >>! 9l <: i32) <: u8)
  in
  let coef10:u8 =
    ((cast (coefficient8 &. 7l <: i32) <: u8) <<! 5l <: u8) |.
    (cast (coefficient7 >>! 6l <: i32) <: u8)
  in
  let coef11:u8 = cast (coefficient8 >>! 3l <: i32) <: u8 in
  coef1, coef2, coef3, coef4, coef5, coef6, coef7, coef8, coef9, coef10, coef11
  <:
  (u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8)

let compress_coefficients_3_ (coefficient1 coefficient2: u16) =
  let coef1:u8 = cast (coefficient1 &. 255us <: u16) <: u8 in
  let coef2:u8 =
    cast ((coefficient1 >>! 8l <: u16) |. ((coefficient2 &. 15us <: u16) <<! 4l <: u16) <: u16)
    <:
    u8
  in
  let coef3:u8 = cast ((coefficient2 >>! 4l <: u16) &. 255us <: u16) <: u8 in
  coef1, coef2, coef3 <: (u8 & u8 & u8)

let compress_coefficients_5_
      (coefficient2 coefficient1 coefficient4 coefficient3 coefficient5 coefficient7 coefficient6 coefficient8:
          u8)
     =
  let coef1:u8 = ((coefficient2 &. 7uy <: u8) <<! 5l <: u8) |. coefficient1 in
  let coef2:u8 =
    (((coefficient4 &. 1uy <: u8) <<! 7l <: u8) |. (coefficient3 <<! 2l <: u8) <: u8) |.
    (coefficient2 >>! 3l <: u8)
  in
  let coef3:u8 = ((coefficient5 &. 15uy <: u8) <<! 4l <: u8) |. (coefficient4 >>! 1l <: u8) in
  let coef4:u8 =
    (((coefficient7 &. 3uy <: u8) <<! 6l <: u8) |. (coefficient6 <<! 1l <: u8) <: u8) |.
    (coefficient5 >>! 4l <: u8)
  in
  let coef5:u8 = (coefficient8 <<! 3l <: u8) |. (coefficient7 >>! 2l <: u8) in
  coef1, coef2, coef3, coef4, coef5 <: (u8 & u8 & u8 & u8 & u8)

let decompress_coefficients_10_ (byte2 byte1 byte3 byte4 byte5: i32) =
  let coefficient1:i32 = ((byte2 &. 3l <: i32) <<! 8l <: i32) |. (byte1 &. 255l <: i32) in
  let coefficient2:i32 = ((byte3 &. 15l <: i32) <<! 6l <: i32) |. (byte2 >>! 2l <: i32) in
  let coefficient3:i32 = ((byte4 &. 63l <: i32) <<! 4l <: i32) |. (byte3 >>! 4l <: i32) in
  let coefficient4:i32 = (byte5 <<! 2l <: i32) |. (byte4 >>! 6l <: i32) in
  coefficient1, coefficient2, coefficient3, coefficient4 <: (i32 & i32 & i32 & i32)

let decompress_coefficients_11_
      (byte2 byte1 byte3 byte5 byte4 byte6 byte7 byte9 byte8 byte10 byte11: i32)
     =
  let coefficient1:i32 = ((byte2 &. 7l <: i32) <<! 8l <: i32) |. byte1 in
  let coefficient2:i32 = ((byte3 &. 63l <: i32) <<! 5l <: i32) |. (byte2 >>! 3l <: i32) in
  let coefficient3:i32 =
    (((byte5 &. 1l <: i32) <<! 10l <: i32) |. (byte4 <<! 2l <: i32) <: i32) |. (byte3 >>! 6l <: i32)
  in
  let coefficient4:i32 = ((byte6 &. 15l <: i32) <<! 7l <: i32) |. (byte5 >>! 1l <: i32) in
  let coefficient5:i32 = ((byte7 &. 127l <: i32) <<! 4l <: i32) |. (byte6 >>! 4l <: i32) in
  let coefficient6:i32 =
    (((byte9 &. 3l <: i32) <<! 9l <: i32) |. (byte8 <<! 1l <: i32) <: i32) |. (byte7 >>! 7l <: i32)
  in
  let coefficient7:i32 = ((byte10 &. 31l <: i32) <<! 6l <: i32) |. (byte9 >>! 2l <: i32) in
  let coefficient8:i32 = (byte11 <<! 3l <: i32) |. (byte10 >>! 5l <: i32) in
  coefficient1,
  coefficient2,
  coefficient3,
  coefficient4,
  coefficient5,
  coefficient6,
  coefficient7,
  coefficient8
  <:
  (i32 & i32 & i32 & i32 & i32 & i32 & i32 & i32)

let decompress_coefficients_4_ (byte: u8) =
  let coefficient1:i32 = cast (byte &. 15uy <: u8) <: i32 in
  let coefficient2:i32 = cast ((byte >>! 4l <: u8) &. 15uy <: u8) <: i32 in
  coefficient1, coefficient2 <: (i32 & i32)

let decompress_coefficients_5_ (byte1 byte2 byte3 byte4 byte5: i32) =
  let coefficient1:i32 = byte1 &. 31l in
  let coefficient2:i32 = ((byte2 &. 3l <: i32) <<! 3l <: i32) |. (byte1 >>! 5l <: i32) in
  let coefficient3:i32 = (byte2 >>! 2l <: i32) &. 31l in
  let coefficient4:i32 = ((byte3 &. 15l <: i32) <<! 1l <: i32) |. (byte2 >>! 7l <: i32) in
  let coefficient5:i32 = ((byte4 &. 1l <: i32) <<! 4l <: i32) |. (byte3 >>! 4l <: i32) in
  let coefficient6:i32 = (byte4 >>! 1l <: i32) &. 31l in
  let coefficient7:i32 = ((byte5 &. 7l <: i32) <<! 2l <: i32) |. (byte4 >>! 6l <: i32) in
  let coefficient8:i32 = byte5 >>! 3l in
  coefficient1,
  coefficient2,
  coefficient3,
  coefficient4,
  coefficient5,
  coefficient6,
  coefficient7,
  coefficient8
  <:
  (i32 & i32 & i32 & i32 & i32 & i32 & i32 & i32)

let compress_then_serialize_10_
      (v_OUT_LEN: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
     =
  let serialized:t_Array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let serialized:t_Array u8 v_OUT_LEN =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact (Rust_primitives.unsize re
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    <:
                    t_Slice i32)
                  (sz 4)
                <:
                Core.Slice.Iter.t_ChunksExact i32)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
      serialized
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 v_OUT_LEN = serialized in
          let i, coefficients:(usize & t_Slice i32) = temp_1_ in
          let coefficient1:i32 =
            Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 10uy
              (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 0 ] <: i32
                  )
                <:
                u16)
          in
          let coefficient2:i32 =
            Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 10uy
              (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 1 ] <: i32
                  )
                <:
                u16)
          in
          let coefficient3:i32 =
            Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 10uy
              (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 2 ] <: i32
                  )
                <:
                u16)
          in
          let coefficient4:i32 =
            Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 10uy
              (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 3 ] <: i32
                  )
                <:
                u16)
          in
          let coef1, coef2, coef3, coef4, coef5:(u8 & u8 & u8 & u8 & u8) =
            compress_coefficients_10_ coefficient1 coefficient2 coefficient3 coefficient4
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              (sz 5 *! i <: usize)
              coef1
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 1 <: usize)
              coef2
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 2 <: usize)
              coef3
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 3 <: usize)
              coef4
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 4 <: usize)
              coef5
          in
          serialized)
  in
  serialized

let compress_then_serialize_11_
      (v_OUT_LEN: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
     =
  let serialized:t_Array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let serialized:t_Array u8 v_OUT_LEN =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact (Rust_primitives.unsize re
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    <:
                    t_Slice i32)
                  (sz 8)
                <:
                Core.Slice.Iter.t_ChunksExact i32)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
      serialized
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 v_OUT_LEN = serialized in
          let i, coefficients:(usize & t_Slice i32) = temp_1_ in
          let coefficient1:i32 =
            Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 11uy
              (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 0 ] <: i32
                  )
                <:
                u16)
          in
          let coefficient2:i32 =
            Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 11uy
              (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 1 ] <: i32
                  )
                <:
                u16)
          in
          let coefficient3:i32 =
            Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 11uy
              (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 2 ] <: i32
                  )
                <:
                u16)
          in
          let coefficient4:i32 =
            Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 11uy
              (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 3 ] <: i32
                  )
                <:
                u16)
          in
          let coefficient5:i32 =
            Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 11uy
              (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 4 ] <: i32
                  )
                <:
                u16)
          in
          let coefficient6:i32 =
            Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 11uy
              (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 5 ] <: i32
                  )
                <:
                u16)
          in
          let coefficient7:i32 =
            Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 11uy
              (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 6 ] <: i32
                  )
                <:
                u16)
          in
          let coefficient8:i32 =
            Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 11uy
              (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 7 ] <: i32
                  )
                <:
                u16)
          in
          let coef1, coef2, coef3, coef4, coef5, coef6, coef7, coef8, coef9, coef10, coef11:(u8 & u8 &
            u8 &
            u8 &
            u8 &
            u8 &
            u8 &
            u8 &
            u8 &
            u8 &
            u8) =
            compress_coefficients_11_ coefficient1
              coefficient2
              coefficient3
              coefficient4
              coefficient5
              coefficient6
              coefficient7
              coefficient8
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              (sz 11 *! i <: usize)
              coef1
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 11 *! i <: usize) +! sz 1 <: usize)
              coef2
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 11 *! i <: usize) +! sz 2 <: usize)
              coef3
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 11 *! i <: usize) +! sz 3 <: usize)
              coef4
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 11 *! i <: usize) +! sz 4 <: usize)
              coef5
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 11 *! i <: usize) +! sz 5 <: usize)
              coef6
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 11 *! i <: usize) +! sz 6 <: usize)
              coef7
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 11 *! i <: usize) +! sz 7 <: usize)
              coef8
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 11 *! i <: usize) +! sz 8 <: usize)
              coef9
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 11 *! i <: usize) +! sz 9 <: usize)
              coef10
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 11 *! i <: usize) +! sz 10 <: usize)
              coef11
          in
          serialized)
  in
  serialized

let compress_then_serialize_4_
      (v_OUT_LEN: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
     =
  let serialized:t_Array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let serialized:t_Array u8 v_OUT_LEN =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact (Rust_primitives.unsize re
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    <:
                    t_Slice i32)
                  (sz 2)
                <:
                Core.Slice.Iter.t_ChunksExact i32)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
      serialized
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 v_OUT_LEN = serialized in
          let i, coefficients:(usize & t_Slice i32) = temp_1_ in
          let coefficient1:u8 =
            cast (Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 4uy
                  (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 0 ]
                        <:
                        i32)
                    <:
                    u16)
                <:
                i32)
            <:
            u8
          in
          let coefficient2:u8 =
            cast (Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 4uy
                  (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 1 ]
                        <:
                        i32)
                    <:
                    u16)
                <:
                i32)
            <:
            u8
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              i
              ((coefficient2 <<! 4l <: u8) |. coefficient1 <: u8)
          in
          serialized)
  in
  serialized

let compress_then_serialize_5_
      (v_OUT_LEN: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
     =
  let serialized:t_Array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let serialized:t_Array u8 v_OUT_LEN =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact (Rust_primitives.unsize re
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    <:
                    t_Slice i32)
                  (sz 8)
                <:
                Core.Slice.Iter.t_ChunksExact i32)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
      serialized
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 v_OUT_LEN = serialized in
          let i, coefficients:(usize & t_Slice i32) = temp_1_ in
          let coefficient1:u8 =
            cast (Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 5uy
                  (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 0 ]
                        <:
                        i32)
                    <:
                    u16)
                <:
                i32)
            <:
            u8
          in
          let coefficient2:u8 =
            cast (Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 5uy
                  (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 1 ]
                        <:
                        i32)
                    <:
                    u16)
                <:
                i32)
            <:
            u8
          in
          let coefficient3:u8 =
            cast (Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 5uy
                  (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 2 ]
                        <:
                        i32)
                    <:
                    u16)
                <:
                i32)
            <:
            u8
          in
          let coefficient4:u8 =
            cast (Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 5uy
                  (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 3 ]
                        <:
                        i32)
                    <:
                    u16)
                <:
                i32)
            <:
            u8
          in
          let coefficient5:u8 =
            cast (Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 5uy
                  (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 4 ]
                        <:
                        i32)
                    <:
                    u16)
                <:
                i32)
            <:
            u8
          in
          let coefficient6:u8 =
            cast (Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 5uy
                  (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 5 ]
                        <:
                        i32)
                    <:
                    u16)
                <:
                i32)
            <:
            u8
          in
          let coefficient7:u8 =
            cast (Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 5uy
                  (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 6 ]
                        <:
                        i32)
                    <:
                    u16)
                <:
                i32)
            <:
            u8
          in
          let coefficient8:u8 =
            cast (Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 5uy
                  (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 7 ]
                        <:
                        i32)
                    <:
                    u16)
                <:
                i32)
            <:
            u8
          in
          let coef1, coef2, coef3, coef4, coef5:(u8 & u8 & u8 & u8 & u8) =
            compress_coefficients_5_ coefficient2
              coefficient1
              coefficient4
              coefficient3
              coefficient5
              coefficient7
              coefficient6
              coefficient8
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              (sz 5 *! i <: usize)
              coef1
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 1 <: usize)
              coef2
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 2 <: usize)
              coef3
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 3 <: usize)
              coef4
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 4 <: usize)
              coef5
          in
          serialized)
  in
  serialized

let compress_then_serialize_message (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement) =
  let serialized:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
  let serialized:t_Array u8 (sz 32) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact (Rust_primitives.unsize re
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    <:
                    t_Slice i32)
                  (sz 8)
                <:
                Core.Slice.Iter.t_ChunksExact i32)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
      serialized
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 (sz 32) = serialized in
          let i, coefficients:(usize & t_Slice i32) = temp_1_ in
          Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
                    (Core.Slice.impl__iter coefficients <: Core.Slice.Iter.t_Iter i32)
                  <:
                  Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter i32))
              <:
              Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter i32))
            serialized
            (fun serialized temp_1_ ->
                let serialized:t_Array u8 (sz 32) = serialized in
                let j, coefficient:(usize & i32) = temp_1_ in
                let coefficient:u16 =
                  Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative coefficient
                in
                let coefficient_compressed:u8 =
                  Libcrux.Kem.Kyber.Compress.compress_message_coefficient coefficient
                in
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
                  i
                  ((serialized.[ i ] <: u8) |. (coefficient_compressed <<! j <: u8) <: u8))
          <:
          t_Array u8 (sz 32))
  in
  serialized

let compress_then_serialize_ring_element_u
      (v_COMPRESSION_FACTOR v_OUT_LEN: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
     =
  let _:Prims.unit = () <: Prims.unit in
  match cast (v_COMPRESSION_FACTOR <: usize) <: pub_u32 with
  | 10ul -> compress_then_serialize_10_ v_OUT_LEN re
  | 11ul -> compress_then_serialize_11_ v_OUT_LEN re
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

let compress_then_serialize_ring_element_v
      (v_COMPRESSION_FACTOR v_OUT_LEN: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
     =
  let _:Prims.unit = () <: Prims.unit in
  match cast (v_COMPRESSION_FACTOR <: usize) <: pub_u32 with
  | 4ul -> compress_then_serialize_4_ v_OUT_LEN re
  | 5ul -> compress_then_serialize_5_ v_OUT_LEN re
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

let deserialize_then_decompress_10_ (serialized: t_Slice u8) =
  let _:Prims.unit = () <: Prims.unit in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact serialized (sz 5) <: Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
      re
      (fun re temp_1_ ->
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = re in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          let byte1:i32 = cast (bytes.[ sz 0 ] <: u8) <: i32 in
          let byte2:i32 = cast (bytes.[ sz 1 ] <: u8) <: i32 in
          let byte3:i32 = cast (bytes.[ sz 2 ] <: u8) <: i32 in
          let byte4:i32 = cast (bytes.[ sz 3 ] <: u8) <: i32 in
          let byte5:i32 = cast (bytes.[ sz 4 ] <: u8) <: i32 in
          let coefficient1, coefficient2, coefficient3, coefficient4:(i32 & i32 & i32 & i32) =
            decompress_coefficients_10_ byte2 byte1 byte3 byte4 byte5
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                (sz 4 *! i <: usize)
                (Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 10uy coefficient1
                  <:
                  i32)
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 4 *! i <: usize) +! sz 1 <: usize)
                (Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 10uy coefficient2
                  <:
                  i32)
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 4 *! i <: usize) +! sz 2 <: usize)
                (Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 10uy coefficient3
                  <:
                  i32)
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 4 *! i <: usize) +! sz 3 <: usize)
                (Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 10uy coefficient4
                  <:
                  i32)
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          re)
  in
  re

let deserialize_then_decompress_11_ (serialized: t_Slice u8) =
  let _:Prims.unit = () <: Prims.unit in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact serialized (sz 11) <: Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
      re
      (fun re temp_1_ ->
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = re in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          let byte1:i32 = cast (bytes.[ sz 0 ] <: u8) <: i32 in
          let byte2:i32 = cast (bytes.[ sz 1 ] <: u8) <: i32 in
          let byte3:i32 = cast (bytes.[ sz 2 ] <: u8) <: i32 in
          let byte4:i32 = cast (bytes.[ sz 3 ] <: u8) <: i32 in
          let byte5:i32 = cast (bytes.[ sz 4 ] <: u8) <: i32 in
          let byte6:i32 = cast (bytes.[ sz 5 ] <: u8) <: i32 in
          let byte7:i32 = cast (bytes.[ sz 6 ] <: u8) <: i32 in
          let byte8:i32 = cast (bytes.[ sz 7 ] <: u8) <: i32 in
          let byte9:i32 = cast (bytes.[ sz 8 ] <: u8) <: i32 in
          let byte10:i32 = cast (bytes.[ sz 9 ] <: u8) <: i32 in
          let byte11:i32 = cast (bytes.[ sz 10 ] <: u8) <: i32 in
          let
          coefficient1,
          coefficient2,
          coefficient3,
          coefficient4,
          coefficient5,
          coefficient6,
          coefficient7,
          coefficient8:(i32 & i32 & i32 & i32 & i32 & i32 & i32 & i32) =
            decompress_coefficients_11_ byte2 byte1 byte3 byte5 byte4 byte6 byte7 byte9 byte8 byte10
              byte11
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                (sz 8 *! i <: usize)
                (Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 11uy coefficient1
                  <:
                  i32)
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 1 <: usize)
                (Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 11uy coefficient2
                  <:
                  i32)
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 2 <: usize)
                (Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 11uy coefficient3
                  <:
                  i32)
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 3 <: usize)
                (Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 11uy coefficient4
                  <:
                  i32)
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 4 <: usize)
                (Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 11uy coefficient5
                  <:
                  i32)
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 5 <: usize)
                (Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 11uy coefficient6
                  <:
                  i32)
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 6 <: usize)
                (Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 11uy coefficient7
                  <:
                  i32)
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 7 <: usize)
                (Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 11uy coefficient8
                  <:
                  i32)
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          re)
  in
  re

let deserialize_then_decompress_4_ (serialized: t_Slice u8) =
  let _:Prims.unit = () <: Prims.unit in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__iter serialized <: Core.Slice.Iter.t_Iter u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter u8))
      re
      (fun re temp_1_ ->
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = re in
          let i, byte:(usize & u8) = temp_1_ in
          let coefficient1, coefficient2:(i32 & i32) = decompress_coefficients_4_ byte in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                (sz 2 *! i <: usize)
                (Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 4uy coefficient1
                  <:
                  i32)
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 2 *! i <: usize) +! sz 1 <: usize)
                (Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 4uy coefficient2
                  <:
                  i32)
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          re)
  in
  re

let deserialize_then_decompress_5_ (serialized: t_Slice u8) =
  let _:Prims.unit = () <: Prims.unit in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact serialized (sz 5) <: Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
      re
      (fun re temp_1_ ->
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = re in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          let byte1:i32 = cast (bytes.[ sz 0 ] <: u8) <: i32 in
          let byte2:i32 = cast (bytes.[ sz 1 ] <: u8) <: i32 in
          let byte3:i32 = cast (bytes.[ sz 2 ] <: u8) <: i32 in
          let byte4:i32 = cast (bytes.[ sz 3 ] <: u8) <: i32 in
          let byte5:i32 = cast (bytes.[ sz 4 ] <: u8) <: i32 in
          let
          coefficient1,
          coefficient2,
          coefficient3,
          coefficient4,
          coefficient5,
          coefficient6,
          coefficient7,
          coefficient8:(i32 & i32 & i32 & i32 & i32 & i32 & i32 & i32) =
            decompress_coefficients_5_ byte1 byte2 byte3 byte4 byte5
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                (sz 8 *! i <: usize)
                (Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 5uy coefficient1
                  <:
                  i32)
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 1 <: usize)
                (Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 5uy coefficient2
                  <:
                  i32)
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 2 <: usize)
                (Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 5uy coefficient3
                  <:
                  i32)
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 3 <: usize)
                (Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 5uy coefficient4
                  <:
                  i32)
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 4 <: usize)
                (Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 5uy coefficient5
                  <:
                  i32)
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 5 <: usize)
                (Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 5uy coefficient6
                  <:
                  i32)
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 6 <: usize)
                (Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 5uy coefficient7
                  <:
                  i32)
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 7 <: usize)
                (Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 5uy coefficient8
                  <:
                  i32)
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          re)
  in
  re

let deserialize_then_decompress_message (serialized: t_Array u8 (sz 32)) =
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Iter.Traits.Collect.f_into_iter serialized
                <:
                Core.Array.Iter.t_IntoIter u8 (sz 32))
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Array.Iter.t_IntoIter u8 (sz 32)))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Array.Iter.t_IntoIter u8 (sz 32)))
      re
      (fun re temp_1_ ->
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = re in
          let i, byte:(usize & u8) = temp_1_ in
          Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                    Core.Ops.Range.f_start = sz 0;
                    Core.Ops.Range.f_end = sz 8
                  }
                  <:
                  Core.Ops.Range.t_Range usize)
              <:
              Core.Ops.Range.t_Range usize)
            re
            (fun re j ->
                let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = re in
                let j:usize = j in
                let coefficient_compressed:i32 = cast ((byte >>! j <: u8) &. 1uy <: u8) <: i32 in
                let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
                  {
                    re with
                    Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      ((sz 8 *! i <: usize) +! j <: usize)
                      (Libcrux.Kem.Kyber.Compress.decompress_message_coefficient coefficient_compressed

                        <:
                        i32)
                  }
                  <:
                  Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
                in
                re)
          <:
          Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
  in
  re

let deserialize_then_decompress_ring_element_u
      (v_COMPRESSION_FACTOR: usize)
      (serialized: t_Slice u8)
     =
  let _:Prims.unit = () <: Prims.unit in
  match cast (v_COMPRESSION_FACTOR <: usize) <: pub_u32 with
  | 10ul -> deserialize_then_decompress_10_ serialized
  | 11ul -> deserialize_then_decompress_11_ serialized
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

let deserialize_then_decompress_ring_element_v
      (v_COMPRESSION_FACTOR: usize)
      (serialized: t_Slice u8)
     =
  let _:Prims.unit = () <: Prims.unit in
  match cast (v_COMPRESSION_FACTOR <: usize) <: pub_u32 with
  | 4ul -> deserialize_then_decompress_4_ serialized
  | 5ul -> deserialize_then_decompress_5_ serialized
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

let deserialize_to_uncompressed_ring_element (serialized: t_Slice u8) =
  let _:Prims.unit = () <: Prims.unit in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact serialized (sz 3) <: Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
      re
      (fun re temp_1_ ->
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = re in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          let byte1:i32 = cast (bytes.[ sz 0 ] <: u8) <: i32 in
          let byte2:i32 = cast (bytes.[ sz 1 ] <: u8) <: i32 in
          let byte3:i32 = cast (bytes.[ sz 2 ] <: u8) <: i32 in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                (sz 2 *! i <: usize)
                (((byte2 &. 15l <: i32) <<! 8l <: i32) |. (byte1 &. 255l <: i32) <: i32)
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 2 *! i <: usize) +! sz 1 <: usize)
                ((byte3 <<! 4l <: i32) |. ((byte2 >>! 4l <: i32) &. 15l <: i32) <: i32)
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          re)
  in
  re

let serialize_uncompressed_ring_element (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement) =
  let serialized:t_Array u8 (sz 384) = Rust_primitives.Hax.repeat 0uy (sz 384) in
  let serialized:t_Array u8 (sz 384) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact (Rust_primitives.unsize re
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    <:
                    t_Slice i32)
                  (sz 2)
                <:
                Core.Slice.Iter.t_ChunksExact i32)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
      serialized
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 (sz 384) = serialized in
          let i, coefficients:(usize & t_Slice i32) = temp_1_ in
          let coefficient1:u16 =
            Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 0 ] <: i32)
          in
          let coefficient2:u16 =
            Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 1 ] <: i32)
          in
          let coef1, coef2, coef3:(u8 & u8 & u8) =
            compress_coefficients_3_ coefficient1 coefficient2
          in
          let serialized:t_Array u8 (sz 384) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              (sz 3 *! i <: usize)
              coef1
          in
          let serialized:t_Array u8 (sz 384) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 3 *! i <: usize) +! sz 1 <: usize)
              coef2
          in
          let serialized:t_Array u8 (sz 384) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 3 *! i <: usize) +! sz 2 <: usize)
              coef3
          in
          serialized)
  in
  serialized
