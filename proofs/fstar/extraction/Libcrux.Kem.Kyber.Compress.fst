module Libcrux.Kem.Kyber.Compress
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let get_n_least_significant_bits (n: u8) (value: u32)
    : Prims.Pure u32
      (requires n >. 0uy && n <. 12uy)
      (ensures
        fun result ->
          let result:u32 = result in
          result <. (Core.Num.impl__u32__pow 2ul (Core.Convert.f_into n <: u32) <: u32)) =
  value &. ((1ul <<! n <: u32) -! 1ul <: u32)

let compress_q (coefficient_bits: u8) (fe: u16)
    : Prims.Pure i32
      (requires
        coefficient_bits >. 0uy && coefficient_bits <=. 11uy &&
        fe <=. (cast (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) <: u16))
      (ensures
        fun result ->
          let result:i32 = result in
          result >=. 0l &&
          result <. (Core.Num.impl__i32__pow 2l (cast (coefficient_bits <: u8) <: u32) <: i32)) =
  let compressed:u32 = (cast (fe <: u16) <: u32) <<! (coefficient_bits +! 1uy <: u8) in
  let compressed:u32 =
    compressed +! (cast (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) <: u32)
  in
  let compressed:u32 =
    compressed /! (cast (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <<! 1l <: i32) <: u32)
  in
  cast (get_n_least_significant_bits coefficient_bits compressed <: u32) <: i32

let decompress_q (coefficient_bits: u8) (fe: i32)
    : Prims.Pure i32
      (requires
        coefficient_bits >. 0uy && coefficient_bits <=. 11uy && fe >=. 0l &&
        fe <. (Core.Num.impl__i32__pow 2l (cast (coefficient_bits <: u8) <: u32) <: i32))
      (ensures
        fun result ->
          let result:i32 = result in
          result <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS) =
  let decompressed:u32 =
    (cast (fe <: i32) <: u32) *! (cast (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) <: u32)
  in
  let decompressed:u32 = (decompressed <<! 1l <: u32) +! (1ul <<! coefficient_bits <: u32) in
  let decompressed:u32 = decompressed >>! (coefficient_bits +! 1uy <: u8) in
  cast (decompressed <: u32) <: i32