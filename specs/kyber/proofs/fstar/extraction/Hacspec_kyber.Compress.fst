module Hacspec_kyber.Compress
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let decompress_d (fe: Hacspec_lib.Field.t_PrimeFieldElement 3329us) (to_bit_size: usize)
    : Hacspec_lib.Field.t_PrimeFieldElement 3329us =
  let _:Prims.unit =
    if ~.(to_bit_size <=. Hacspec_kyber.Parameters.v_BITS_PER_COEFFICIENT <: bool)
    then
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: to_bit_size <= parameters::BITS_PER_COEFFICIENT"

          <:
          Rust_primitives.Hax.t_Never)
  in
  let decompressed:u32 =
    (((2ul *! (Core.Convert.f_from fe.Hacspec_lib.Field.f_value <: u32) <: u32) *!
        (Core.Convert.f_from Hacspec_lib.Field.impl_2__MODULUS_1 <: u32)
        <:
        u32) +!
      (1ul <<! to_bit_size <: u32)
      <:
      u32) >>!
    (to_bit_size +! sz 1 <: usize)
  in
  Core.Convert.f_into decompressed

let decompress
      (re:
          Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            (sz 256))
      (bits_per_compressed_coefficient: usize)
    : Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
      (sz 256) =
  Hacspec_lib.Ring.impl_2__new (sz 256)
    (Core.Array.impl_23__map (sz 256)
        (Hacspec_lib.Ring.impl_2__coefficients (sz 256) re
          <:
          t_Array (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256))
        (fun coefficient ->
            let coefficient:Hacspec_lib.Field.t_PrimeFieldElement 3329us = coefficient in
            decompress_d coefficient bits_per_compressed_coefficient
            <:
            Hacspec_lib.Field.t_PrimeFieldElement 3329us)
      <:
      t_Array (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256))

let compress_d (fe: Hacspec_lib.Field.t_PrimeFieldElement 3329us) (to_bit_size: usize)
    : Hacspec_lib.Field.t_PrimeFieldElement 3329us =
  let _:Prims.unit =
    if ~.(to_bit_size <=. Hacspec_kyber.Parameters.v_BITS_PER_COEFFICIENT <: bool)
    then
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: to_bit_size <= parameters::BITS_PER_COEFFICIENT"

          <:
          Rust_primitives.Hax.t_Never)
  in
  let two_pow_bit_size:u32 =
    Core.Num.impl__u32__pow 2ul
      (Core.Result.impl__unwrap_or_else (Core.Convert.f_try_into to_bit_size
            <:
            Core.Result.t_Result u32 Core.Num.Error.t_TryFromIntError)
          (fun temp_0_ ->
              let _:Core.Num.Error.t_TryFromIntError = temp_0_ in
              Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.impl_2__new_v1 (Rust_primitives.unsize
                            (let list =
                                [
                                  "Conversion should work since to_bit_size is never greater than ";
                                  "."
                                ]
                              in
                              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                              Rust_primitives.Hax.array_of_list list)
                          <:
                          t_Slice string)
                        (Rust_primitives.unsize (let list =
                                [
                                  Core.Fmt.Rt.impl_1__new_display Hacspec_kyber.Parameters.v_BITS_PER_COEFFICIENT

                                  <:
                                  Core.Fmt.Rt.t_Argument
                                ]
                              in
                              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                              Rust_primitives.Hax.array_of_list list)
                          <:
                          t_Slice Core.Fmt.Rt.t_Argument)
                      <:
                      Core.Fmt.t_Arguments)
                  <:
                  Rust_primitives.Hax.t_Never)
              <:
              u32)
        <:
        u32)
  in
  let compressed:u32 =
    ((((Core.Convert.f_from fe.Hacspec_lib.Field.f_value <: u32) *! 2ul <: u32) *! two_pow_bit_size
        <:
        u32) +!
      (Core.Convert.f_from Hacspec_lib.Field.impl_2__MODULUS_1 <: u32)
      <:
      u32) /!
    (Core.Convert.f_from (2us *! Hacspec_lib.Field.impl_2__MODULUS_1 <: u16) <: u32)
  in
  Core.Convert.f_into (compressed %! two_pow_bit_size <: u32)

let compress
      (re:
          Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            (sz 256))
      (bits_per_compressed_coefficient: usize)
    : Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
      (sz 256) =
  Hacspec_lib.Ring.impl_2__new (sz 256)
    (Core.Array.impl_23__map (sz 256)
        (Hacspec_lib.Ring.impl_2__coefficients (sz 256) re
          <:
          t_Array (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256))
        (fun coefficient ->
            let coefficient:Hacspec_lib.Field.t_PrimeFieldElement 3329us = coefficient in
            compress_d coefficient bits_per_compressed_coefficient
            <:
            Hacspec_lib.Field.t_PrimeFieldElement 3329us)
      <:
      t_Array (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256))
