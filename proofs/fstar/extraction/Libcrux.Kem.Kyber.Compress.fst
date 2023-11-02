module Libcrux.Kem.Kyber.Compress
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let compress_q (#v_COEFFICIENT_BITS: usize) (fe: u16)
    : Prims.Pure i32
      (requires
        v_COEFFICIENT_BITS <=. sz 11 &&
        (Core.Convert.f_from fe <: i32) <=. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS)
      (ensures
        fun result -> result >=. 0l && result <=. ((1l <<! v_COEFFICIENT_BITS <: i32) -! 1l <: i32)) =
  let compressed:u32 = (cast fe <: u32) <<! (v_COEFFICIENT_BITS +! sz 1 <: usize) in
  let compressed:u32 = compressed +! (cast Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: u32) in
  let compressed:u32 =
    compressed /! (cast (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <<! 1l <: i32) <: u32)
  in
  cast (compressed &. ((1ul <<! v_COEFFICIENT_BITS <: u32) -! 1ul <: u32)) <: i32

let decompress_q (#v_COEFFICIENT_BITS: usize) (fe: i32)
    : Prims.Pure i32
      (requires
        v_COEFFICIENT_BITS <=. sz 11 && fe >=. 0l && fe <. (1l <<! v_COEFFICIENT_BITS <: i32))
      (ensures fun result -> result <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS) =
  let decompressed:u32 =
    (cast fe <: u32) *! (cast Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: u32)
  in
  let decompressed:u32 = (decompressed <<! 1l <: u32) +! (1ul <<! v_COEFFICIENT_BITS <: u32) in
  let decompressed:u32 = decompressed >>! (v_COEFFICIENT_BITS +! sz 1 <: usize) in
  cast decompressed <: i32

let decompress
      (#v_COEFFICIENT_BITS: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
    : Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    {
      re with
      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
      =
      Core.Array.impl_23__map re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
        (fun coefficient -> decompress_q coefficient <: i32)
    }
  in
  re