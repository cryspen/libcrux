module Libcrux.Kem.Kyber.Serialize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 150"
open Core
open FStar.Mul

open Libcrux.Kem.Kyber.Arithmetic

open MkSeq

#push-options "--fuel 0 --ifuel 1 --z3rlimit 100"
let compress_coefficients_10_ (coefficient1 coefficient2 coefficient3 coefficient4: i32) =
  let coef1:u8 = cast (coefficient1 &. 255l <: i32) <: u8 in // coefficient1[0-8]
  let coef2:u8 =
    ((cast (coefficient2 &. 63l <: i32) <: u8) <<! 2l <: u8) |.
    (cast ((coefficient1 >>! 8l <: i32) &. 3l <: i32) <: u8) // 8-10
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
  let result = coef1, coef2, coef3, coef4, coef5 <: (u8 & u8 & u8 & u8 & u8) in
  result
#pop-options

#push-options "--fuel 0 --ifuel 1 --z3rlimit 300"
let compress_coefficients_11_
      coefficient1 coefficient2 coefficient3 coefficient4 coefficient5 coefficient6 coefficient7 coefficient8 =
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
#pop-options

#push-options "--fuel 0 --ifuel 1 --z3rlimit 40"
let compress_coefficients_3_ coefficient1 coefficient2 =
  let coef1:u8 = cast (coefficient1 &. 255us <: u16) <: u8 in
  get_bit_pow2_minus_one_u16 255 (sz 0);
  let coef2:u8 =
    cast ((coefficient1 >>! 8l <: u16) |. ((coefficient2 &. 15us <: u16) <<! 4l <: u16) <: u16)
    <:
    u8
  in
  let coef3:u8 = cast ((coefficient2 >>! 4l <: u16) &. 255us <: u16) <: u8 in
  coef1, coef2, coef3 <: (u8 & u8 & u8) 
#pop-options

#push-options "--fuel 0 --ifuel 1 --z3rlimit 160"
let compress_coefficients_5_
      coefficient2 coefficient1 coefficient4 coefficient3 coefficient5 coefficient7 coefficient6 coefficient8
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
#pop-options

#push-options "--fuel 0 --ifuel 1 --z3rlimit 40 --split_queries always"
let decompress_coefficients_10_ byte2 byte1 byte3 byte4 byte5 =
  let coefficient1:i32 = ((byte2 &. 3l <: i32) <<! 8l <: i32) |. (byte1 &. 255l <: i32) in
  let coefficient2:i32 = ((byte3 &. 15l <: i32) <<! 6l <: i32) |. (byte2 >>! 2l <: i32) in
  let coefficient3:i32 = ((byte4 &. 63l <: i32) <<! 4l <: i32) |. (byte3 >>! 4l <: i32) in
  let coefficient4:i32 = (byte5 <<! 2l <: i32) |. (byte4 >>! 6l <: i32) in
  coefficient1, coefficient2, coefficient3, coefficient4 <: (i32 & i32 & i32 & i32)
#pop-options

#push-options "--fuel 0 --ifuel 1 --z3rlimit 260"
let decompress_coefficients_11_
      byte2 byte1 byte3 byte5 byte4 byte6 byte7 byte9 byte8 byte10 byte11 =
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
#pop-options

#push-options "--fuel 0 --ifuel 1 --z3rlimit 40"
let decompress_coefficients_4_ byte =
  let coefficient1:i32 = cast (byte &. 15uy <: u8) <: i32 in
  let coefficient2:i32 = cast ((byte >>! 4l <: u8) &. 15uy <: u8) <: i32 in
  coefficient1, coefficient2 <: (i32 & i32)
#pop-options

#push-options "--fuel 0 --ifuel 1 --z3rlimit 100"
let decompress_coefficients_5_ byte1 byte2 byte3 byte4 byte5 =
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
#pop-options

