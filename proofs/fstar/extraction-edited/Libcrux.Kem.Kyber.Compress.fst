module Libcrux.Kem.Kyber.Compress
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let compress_message_coefficient (fe: u16) =
  let (shifted: i16):i16 = 1664s -! (cast (fe <: u16) <: i16) in
  let mask:i16 = shifted >>! 15l in
  let shifted_to_positive:i16 = mask ^. shifted in
  assume (shifted_to_positive >=. 0s);
  let shifted_positive_in_range:i16 = shifted_to_positive -! 832s in
  let res = cast ((shifted_positive_in_range >>! 15l <: i16) &. 1s <: i16) <: u8 in
  admit(); //P-F
  res

let compress_ciphertext_coefficient (coefficient_bits: u8) (fe: u16) =
  let _:Prims.unit = () <: Prims.unit in
  let _:Prims.unit = () <: Prims.unit in
  let compressed:u32 = (cast (fe <: u16) <: u32) <<! (coefficient_bits +! 1uy <: u8) in
  let compressed:u32 =
    compressed +! (cast (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) <: u32)
  in
  let compressed:u32 =
    compressed /! (cast (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <<! 1l <: i32) <: u32)
  in
  let res = cast (Libcrux.Kem.Kyber.Arithmetic.get_n_least_significant_bits coefficient_bits compressed <: u32
    )
  <:
  i32
  in
  admit(); // P-F
  res

let decompress_ciphertext_coefficient (coefficient_bits: u8) (fe: i32) =
  let _:Prims.unit = () <: Prims.unit in
  let _:Prims.unit = () <: Prims.unit in
  assert (v (1ul <<! coefficient_bits) <= pow2 11);
  assert (v fe < pow2 11);
  let decompressed:u32 =
    (cast (fe <: i32) <: u32) *! (cast (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) <: u32)
  in
  let decompressed:u32 = (decompressed <<! 1l <: u32) +! (1ul <<! coefficient_bits <: u32) in
  let decompressed:u32 = decompressed >>! (coefficient_bits +! 1uy <: u8) in
  let res = cast (decompressed <: u32) <: i32 in
  admit(); // P-F
  res

let decompress_message_coefficient (fe: i32) =
  (Core.Ops.Arith.Neg.neg fe <: i32) &.
  ((Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS +! 1l <: i32) /! 2l <: i32)
