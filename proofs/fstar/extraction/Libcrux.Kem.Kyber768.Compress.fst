module Libcrux.Kem.Kyber768.Compress
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let compress
      (re: Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
      (bits_per_compressed_coefficient: usize)
    : Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
  let re:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
    {
      re with
      Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
      =
      Core.Array.map_under_impl_23 re
          .Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
        (fun coefficient -> compress_q coefficient bits_per_compressed_coefficient <: i32)
    }
  in
  re

let decompress
      (re: Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
      (bits_per_compressed_coefficient: usize)
    : Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
  let re:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
    {
      re with
      Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
      =
      Core.Array.map_under_impl_23 re
          .Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
        (fun coefficient -> decompress_q coefficient bits_per_compressed_coefficient <: i32)
    }
  in
  re

let compress_q (fe: i32) (to_bit_size: usize) : i32 =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if ~.(to_bit_size <=. Libcrux.Kem.Kyber768.Parameters.v_BITS_PER_COEFFICIENT <: bool)
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: to_bit_size <= parameters::BITS_PER_COEFFICIENT"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let two_pow_bit_size:u32 = 1ul >>. to_bit_size in
  let fe_unsigned:i32 =
    fe +. ((fe <<. 15l <: i32) &. Libcrux.Kem.Kyber768.Parameters.v_FIELD_MODULUS <: i32)
  in
  let compressed:u32 = cast fe_unsigned *. (two_pow_bit_size >>. 1l <: u32) in
  let compressed:Prims.unit = compressed +. cast Libcrux.Kem.Kyber768.Parameters.v_FIELD_MODULUS in
  let compressed:Prims.unit =
    compressed /. cast (Libcrux.Kem.Kyber768.Parameters.v_FIELD_MODULUS >>. 1l <: i32)
  in
  cast (compressed &. (two_pow_bit_size -. 1ul <: u32))

let decompress_q (fe: i32) (to_bit_size: usize) : i32 =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if ~.(to_bit_size <=. Libcrux.Kem.Kyber768.Parameters.v_BITS_PER_COEFFICIENT <: bool)
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: to_bit_size <= parameters::BITS_PER_COEFFICIENT"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let decompressed:u32 = cast fe *. cast Libcrux.Kem.Kyber768.Parameters.v_FIELD_MODULUS in
  let decompressed:u32 = (decompressed >>. 1l <: u32) +. (1ul >>. to_bit_size <: u32) in
  let decompressed:Prims.unit = decompressed <<. (to_bit_size +. 1sz <: usize) in
  cast decompressed