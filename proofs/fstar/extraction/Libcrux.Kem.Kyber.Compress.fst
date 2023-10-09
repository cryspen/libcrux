module Libcrux.Kem.Kyber.Compress
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let compress
      (#v_COEFFICIENT_BITS: u32)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
    : Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    {
      re with
      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
      =
      Core.Array.impl_23__map re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
        (fun coefficient ->
            compress_q (Libcrux.Kem.Kyber.Conversions.to_unsigned_representative coefficient <: u16)
            <:
            i32)
    }
  in
  re

let decompress
      (re: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
      (bits_per_compressed_coefficient: usize)
    : Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    {
      re with
      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
      =
      Core.Array.impl_23__map re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
        (fun coefficient -> decompress_q coefficient bits_per_compressed_coefficient <: i32)
    }
  in
  re

let compress_q (#v_COEFFICIENT_BITS: u32) (fe: u16) : i32 =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if
          ~.((cast v_COEFFICIENT_BITS <: usize) <=.
            Libcrux.Kem.Kyber.Constants.v_BITS_PER_COEFFICIENT
            <:
            bool)
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: COEFFICIENT_BITS as usize <= BITS_PER_COEFFICIENT"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let two_pow_bit_size:u32 = 1ul <<! v_COEFFICIENT_BITS in
  let compressed:u32 = (cast fe <: u32) *! (two_pow_bit_size <<! 1l <: u32) in
  let compressed:Prims.unit =
    compressed +! (cast Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: u32)
  in
  let compressed:Prims.unit =
    compressed /! (cast (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <<! 1l <: i32) <: u32)
  in
  cast (compressed &. (two_pow_bit_size -! 1ul <: u32)) <: i32

let decompress_q (fe: i32) (to_bit_size: usize) : i32 =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if ~.(to_bit_size <=. Libcrux.Kem.Kyber.Constants.v_BITS_PER_COEFFICIENT <: bool)
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: to_bit_size <= BITS_PER_COEFFICIENT"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let decompressed:u32 =
    (cast fe <: u32) *! (cast Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: u32)
  in
  let decompressed:u32 = (decompressed <<! 1l <: u32) +! (1ul <<! to_bit_size <: u32) in
  let decompressed:Prims.unit = decompressed >>! (to_bit_size +! sz 1 <: usize) in
  cast decompressed <: i32