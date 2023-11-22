module Libcrux.Kem.Kyber.Compress
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let compress_message_coefficient (fe: u16)
    : Prims.Pure u8
      (requires fe <. (cast (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) <: u16))
      (fun _ -> Prims.l_True) =
  let (shifted: i16):i16 = 1664s -! (cast (fe <: u16) <: i16) in
  let shifted_to_positive:i16 = (shifted >>! 15l <: i16) ^. shifted in
  let shifted_positive_in_range:i16 = shifted_to_positive -! 832s in
  cast ((shifted_positive_in_range >>! 15l <: i16) &. 1s <: i16) <: u8

let get_n_least_significant_bits (n: u8) (value: u32)
    : Prims.Pure u32
      (requires n >. 0uy && n <=. 11uy)
      (ensures
        fun result ->
          let result:u32 = result in
          result <. (Core.Num.impl__u32__pow 2ul (Core.Convert.f_into n <: u32) <: u32)) =
  let _:Prims.unit = () <: Prims.unit in
  value &. ((1ul <<! n <: u32) -! 1ul <: u32)

let compress_ciphertext_coefficient (coefficient_bits: u8) (fe: u16)
    : Prims.Pure i32
      (requires
        coefficient_bits >. 0uy && coefficient_bits <=. 11uy &&
        fe <. (cast (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) <: u16))
      (ensures
        fun result ->
          let result:i32 = result in
          result >=. 0l &&
          result <. (Core.Num.impl__i32__pow 2l (cast (coefficient_bits <: u8) <: u32) <: i32)) =
  let _:Prims.unit = () <: Prims.unit in
  let _:Prims.unit = () <: Prims.unit in
  let compressed:u32 = (cast (fe <: u16) <: u32) <<! (coefficient_bits +! 1uy <: u8) in
  let compressed:u32 =
    compressed +! (cast (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) <: u32)
  in
  let compressed:u32 =
    compressed /! (cast (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <<! 1l <: i32) <: u32)
  in
  cast (get_n_least_significant_bits coefficient_bits compressed <: u32) <: i32

let decompress_ciphertext_coefficient (coefficient_bits: u8) (fe: i32)
    : Prims.Pure i32
      (requires
        coefficient_bits >. 0uy && coefficient_bits <=. 11uy && fe >=. 0l &&
        fe <. (Core.Num.impl__i32__pow 2l (cast (coefficient_bits <: u8) <: u32) <: i32))
      (ensures
        fun result ->
          let result:i32 = result in
          result <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS) =
  let _:Prims.unit = () <: Prims.unit in
  let _:Prims.unit = () <: Prims.unit in
  let decompressed:u32 =
    (cast (fe <: i32) <: u32) *! (cast (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) <: u32)
  in
  let decompressed:u32 = (decompressed <<! 1l <: u32) +! (1ul <<! coefficient_bits <: u32) in
  let decompressed:u32 = decompressed >>! (coefficient_bits +! 1uy <: u8) in
  cast (decompressed <: u32) <: i32

let decompress_message_coefficient (fe: i32)
    : Prims.Pure i32 (requires fe =. 0l || fe =. 1l) (fun _ -> Prims.l_True) =
  (Core.Ops.Arith.Neg.neg fe <: i32) &.
  ((Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS +! 1l <: i32) /! 2l <: i32)
