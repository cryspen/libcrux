module Libcrux.Kem.Kyber.Compress
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let compress_q (coefficient_bits: u32) (fe: u16)
    : Prims.Pure i32
      (requires
        coefficient_bits <=. 11ul &&
        fe <=. (cast Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: u16))
      (fun _ -> Prims.l_True) =
  let compressed:u32 = (cast fe <: u32) <<! (coefficient_bits +! 1ul <: u32) in
  let compressed:u32 = compressed +! (cast Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: u32) in
  let compressed:u32 =
    compressed /! (cast (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <<! 1l <: i32) <: u32)
  in
  cast (compressed &. ((1ul <<! coefficient_bits <: u32) -! 1ul <: u32)) <: i32

let decompress_q (coefficient_bits: u32) (fe: i32)
    : Prims.Pure i32
      (requires coefficient_bits <=. 11ul && fe >=. 0l && fe <. (1l <<! coefficient_bits <: i32))
      (ensures fun result -> result <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS) =
  let decompressed:u32 =
    (cast fe <: u32) *! (cast Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: u32)
  in
  let decompressed:u32 = (decompressed <<! 1l <: u32) +! (1ul <<! coefficient_bits <: u32) in
  let decompressed:u32 = decompressed >>! (coefficient_bits +! 1ul <: u32) in
  cast decompressed <: i32