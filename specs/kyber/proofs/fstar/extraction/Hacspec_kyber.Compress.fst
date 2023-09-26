module Hacspec_kyber.Compress
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let compress
      (re:
          Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            256sz)
      (bits_per_compressed_coefficient: usize)
    : Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz =
  Hacspec_lib.Ring.new_under_impl_2 (Core.Array.map_under_impl_23 (Hacspec_lib.Ring.coefficients_under_impl_2
            re
          <:
          array (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz)
        (fun coefficient ->
            compress_d coefficient bits_per_compressed_coefficient
            <:
            Hacspec_lib.Field.t_PrimeFieldElement 3329us)
      <:
      array (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz)

let decompress
      (re:
          Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            256sz)
      (bits_per_compressed_coefficient: usize)
    : Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz =
  Hacspec_lib.Ring.new_under_impl_2 (Core.Array.map_under_impl_23 (Hacspec_lib.Ring.coefficients_under_impl_2
            re
          <:
          array (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz)
        (fun coefficient ->
            decompress_d coefficient bits_per_compressed_coefficient
            <:
            Hacspec_lib.Field.t_PrimeFieldElement 3329us)
      <:
      array (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz)

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
    Core.Num.pow_under_impl_8 2ul
      (Core.Result.unwrap_or_else_under_impl (Core.Convert.TryInto.try_into to_bit_size
            <:
            Core.Result.t_Result u32 _)
          (fun _ ->
              Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2
                        (Rust_primitives.unsize (let list =
                                [
                                  "Conversion should work since to_bit_size is never greater than ";
                                  "."
                                ]
                              in
                              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                              Rust_primitives.Hax.array_of_list list)
                          <:
                          slice string)
                        (Rust_primitives.unsize (let list =
                                [
                                  Core.Fmt.Rt.new_display_under_impl_1 Hacspec_kyber.Parameters.v_BITS_PER_COEFFICIENT

                                  <:
                                  Core.Fmt.Rt.t_Argument
                                ]
                              in
                              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                              Rust_primitives.Hax.array_of_list list)
                          <:
                          slice Core.Fmt.Rt.t_Argument)
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
    ((((Core.Convert.From.from fe.Hacspec_lib.Field.PrimeFieldElement.f_value <: u32) *. 2ul <: u32) *.
        two_pow_bit_size
        <:
        u32) +.
      (Core.Convert.From.from Hacspec_lib.Field.v_MODULUS_1_under_impl_2 <: u32)
      <:
      u32) /.
    (Core.Convert.From.from (2us *. Hacspec_lib.Field.v_MODULUS_1_under_impl_2 <: u16) <: u32)
  in
  Core.Convert.Into.into (compressed %. two_pow_bit_size <: u32)

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
    (((2ul *. (Core.Convert.From.from fe.Hacspec_lib.Field.PrimeFieldElement.f_value <: u32) <: u32) *.
        (Core.Convert.From.from Hacspec_lib.Field.v_MODULUS_1_under_impl_2 <: u32)
        <:
        u32) +.
      (1ul >>. to_bit_size <: u32)
      <:
      u32) <<.
    (to_bit_size +. 1sz <: usize)
  in
  Core.Convert.Into.into decompressed