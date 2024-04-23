module Libcrux_ml_kem.Compress
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let compress_ciphertext_coefficient (coefficient_bits: u8) (fe: u16) =
  let compressed:u64 = (cast (fe <: u16) <: u64) <<! coefficient_bits in
  let compressed:u64 = compressed +! 1664uL in
  let compressed:u64 = compressed *! 10321340uL in
  let compressed:u64 = compressed >>! 35l in
  cast (Libcrux_ml_kem.Arithmetic.get_n_least_significant_bits coefficient_bits
        (cast (compressed <: u64) <: u32)
      <:
      u32)
  <:
  i32

let compress_message_coefficient (fe: u16) =
  let (shifted: i16):i16 = 1664s -! (cast (fe <: u16) <: i16) in
  let mask:i16 = shifted >>! 15l in
  let shifted_to_positive:i16 = mask ^. shifted in
  let shifted_positive_in_range:i16 = shifted_to_positive -! 832s in
  cast ((shifted_positive_in_range >>! 15l <: i16) &. 1s <: i16) <: u8
